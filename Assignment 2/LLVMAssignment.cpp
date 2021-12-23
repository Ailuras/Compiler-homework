#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Pass.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>
#include <llvm/IR/Instructions.h>
#include <list>
#include <map>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>

using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
struct EnableFunctionOptPass: public FunctionPass {
    static char ID;
    EnableFunctionOptPass():FunctionPass(ID){}
    bool runOnFunction(Function & F) override{
        if(F.hasFnAttribute(Attribute::OptimizeNone)) F.removeFnAttr(Attribute::OptimizeNone);
        return true;
    }
};
char EnableFunctionOptPass::ID = 0;
struct FuncPtrPass : public ModulePass {
    static char ID;
    FuncPtrPass() : ModulePass(ID) {}
	std::map<int, std::list<Function*>> result;
    bool runOnModule(Module &M) override {
		for(Module::iterator i = M.begin(); i != M.end(); i++) {
			for(Function::iterator j = i->begin(); j != i->end(); j++) {
				for(BasicBlock::iterator k = j->begin(); k != j->end(); k++) {
					if(CallInst *callInst = dyn_cast<CallInst>(k)) {
						int line = callInst->getDebugLoc().getLine();
						if(Function *func = callInst->getCalledFunction()) result[line].push_back(func);
						else if(Value *value = callInst->getCalledOperand()) result[line].splice(result[line].end(), std::list<Function*>(solveValue(value)));
						else errs() << "ERROR\n";
					}
				}
			}
		}
		for(std::map<int, std::list<Function*>>::iterator i = result.begin(); i != result.end(); i++) {
			if(i->first == 0) continue;
			errs() << i->first << " : ";
			i->second.sort(); i->second.unique();
			std::list<Function*>::iterator funcEnd = --(i->second.end());
			for(std::list<Function*>::iterator func = i->second.begin(); func != funcEnd; ++func) errs()<<(*func)->getName()<<',';
			errs()<<(*funcEnd)->getName()<<'\n';
		}
        return false;
    }
	std::list<Function*> solveFunction(CallInst *caller, Function *func, std::list<Value*> values, BasicBlock* basicBlock) {
		std::list<Function*> res;
		while(!values.empty()) {
			Value *value = values.front();
			if(Function *theFunc = dyn_cast<Function>(value)) {
				res.push_back(theFunc);
			}else if (CallInst *callInst = dyn_cast<CallInst>(value)) {
				errs() << "UNIMPLEMNTED\n";
			}else if(PHINode *phi = dyn_cast<PHINode>(value)) {
				for(Value *phivalue : phi->incoming_values())
					values.push_back(phivalue);
			}else if(Argument *arg = dyn_cast<Argument>(value)) {
				unsigned argIdx = arg->getArgNo();
				BasicBlock *curBlock = caller->getParent();
				Value *valueToSolve = caller->getArgOperand(std::move(argIdx));
				valueToSolve = valueToSolve->DoPHITranslation(std::move(curBlock), basicBlock);
				std::list<Function*> solveValueRes = solveValue(std::move(valueToSolve));
				res.splice(res.end(), solveValueRes);
			}
			values.pop_front();
		}
		return res;
	}
	std::list<Value*> getReturnVal(Function *func) {
		std::list<Value*> res;
		for (Function::iterator i = func->begin(); i != func->end(); i++) if (ReturnInst *ret = dyn_cast<ReturnInst>(i->getTerminator())) res.push_back(ret->getReturnValue());
		return res;
	}
	std::list<Function*> solveValue(Value *origin) {
		std::list<Function*> res;
		std::list<Value*> solveRes;
		solveRes.push_back(origin);
		while(!solveRes.empty()) {
			Value *value = solveRes.front();
			if(Function *theFunc = dyn_cast<Function>(value)) res.push_back(theFunc);
			// else if(CallInst *callInst = dyn_cast<CallInst>(value)) res.splice(res.end(), solveReturnVal(callInst));
			else if(CallInst *callInst = dyn_cast<CallInst>(value)) {
				std::list<Function*> tmp;
				if(Function *doubleCall = callInst->getCalledFunction()) {
					std::list<Value*> valuesToSolve = getReturnVal(doubleCall);
					tmp.splice(tmp.end(), solveFunction(callInst, doubleCall, std::move(valuesToSolve), callInst->getParent()));
				}else if(PHINode *phi = dyn_cast<PHINode>(callInst->getCalledOperand())) {
					for (BasicBlock *block : phi->blocks()) {
						std::list<Function*> solveTheVal = solveValue(phi->getIncomingValueForBlock(block));
						for (Function *func : solveTheVal) {
							std::list<Value*> valuesToSolve = getReturnVal(func);
							tmp.splice(tmp.end(), solveFunction(callInst, func, std::move(valuesToSolve), block));
						}
					}
				}else for(Function *func : solveValue(callInst->getCalledOperand())) res.splice(res.end(), solveFunction(callInst, func, std::move(getReturnVal(func)), callInst->getParent()));
				res.splice(res.end(), tmp);
			}else if(PHINode *phi = dyn_cast<PHINode>(value)) for(Value *phivalue : phi->incoming_values()) solveRes.push_back(phivalue);
			else if(Argument *arg = dyn_cast<Argument>(value)) {
				std::list<Function*> temp;
				unsigned argIdx = arg->getArgNo();
				for(User *user : arg->getParent()->users()) {
					if(CallInst *callInst = dyn_cast<CallInst>(user)) {
						if(arg->getParent() == callInst->getCalledFunction()) {
							Value *valueToSolve = callInst->getArgOperand(argIdx);
							temp.splice(temp.end(), solveValue(valueToSolve));
						}else {
							int argNumber = callInst->getNumArgOperands();
							for(int i = 0; i < argNumber; ++i) {
								if(arg->getParent() == dyn_cast<Function>(callInst->getArgOperand(i))) {
									auto calledFunctions = solveValue(callInst->getCalledOperand());
									for(Function *func : calledFunctions) {
										std::list<Value*> temp2;
										for(Function::iterator i = func->begin(); i != func->end(); i++) {
											for(BasicBlock::iterator j = i->begin(); j != i->end(); j++) {
												if(CallInst *k = dyn_cast<CallInst>(j)) {
													if(Argument* calledArg = dyn_cast<Argument>(k->getCalledOperand())) {
														if(calledArg->getArgNo() == argIdx) temp2.push_back(k->getArgOperand(argIdx));
													}
												}
											}
										}
										auto valuesToSolve = temp2;
										temp.splice(temp.end(), solveFunction(callInst, func, valuesToSolve, callInst->getParent()));
									}
								}
							}
						}
					}else errs()<<"for argument user, not a call instruction!\n";
				}
				res.splice(res.end(), temp);
			}else if(ConstantPointerNull *nptr = dyn_cast<ConstantPointerNull>(value)) {}
			else if(SelectInst *selectInst = dyn_cast<SelectInst>(value)) {
				if(CmpInst *cmpInst = dyn_cast<CmpInst>(selectInst->getCondition())) {
					Value *operand0 = cmpInst->getOperand(0), *operand1 = cmpInst->getOperand(1);
					ConstantInt *temp;
					if((temp = dyn_cast<ConstantInt>(operand0)) && (temp = dyn_cast<ConstantInt>(operand1))) {
						int64_t item0 = dyn_cast<ConstantInt>(operand0)->getSExtValue();
						int64_t item1 = dyn_cast<ConstantInt>(operand1)->getSExtValue();
						switch(cmpInst->getPredicate()) {
							case CmpInst::ICMP_SGE: if(item0 >= item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_SLT: if(item0 < item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_EQ: if(item0 == item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_NE: if(item0 != item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_SLE: if(item0 <= item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_SGT: if(item0 > item1) solveRes.push_back(selectInst->getTrueValue()); break;
							case CmpInst::ICMP_UGT:
							case CmpInst::ICMP_UGE:
							case CmpInst::ICMP_ULT:
							case CmpInst::ICMP_ULE:
							default: solveRes.push_back(selectInst->getFalseValue()); break;
						};
					}else {
						solveRes.push_back(selectInst->getTrueValue());
						solveRes.push_back(selectInst->getFalseValue());
					}
				}
			}else errs()<<"ERROR here\n";
			solveRes.pop_front();
		}
		return res;
	}
};
char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");
static cl::opt<std::string> InputFilename(cl::Positional, cl::desc("<filename>.bc"), cl::init(""));

int main(int argc, char **argv) {
    LLVMContext &Context = getGlobalContext();
    SMDiagnostic Err;
    cl::ParseCommandLineOptions(argc, argv, "FuncPtrPass \n My first LLVM too which does not do much.\n");
    std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
    if (!M) {
        Err.print(argv[0], errs());
        return 1;
    }
    llvm::legacy::PassManager Passes;
    Passes.add(new EnableFunctionOptPass());
    Passes.add(llvm::createPromoteMemoryToRegisterPass());
	  Passes.add(llvm::createCFGSimplificationPass());
    Passes.add(new FuncPtrPass());
    Passes.run(*M.get());
}