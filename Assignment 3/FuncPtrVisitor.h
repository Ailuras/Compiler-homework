#include <llvm/IR/Function.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <iostream>
#include <list>
#include "Dataflow.h"
using namespace llvm;
typedef std::map<Value*, std::set<Value*>> Pointer2Set;

struct PointerInfo {
    Pointer2Set ps;
    Pointer2Set ps_field;
    PointerInfo() : ps(), ps_field() {}
    PointerInfo(const PointerInfo& info) : ps(info.ps), ps_field(info.ps_field) {}
    bool operator==(const PointerInfo& info) const { return ps == info.ps && ps_field == info.ps_field; }
};

inline raw_ostream& operator<<(raw_ostream& out, const Pointer2Set& ps) {
    out<<"{ ";
    for(auto i=ps.begin(); i!=ps.end(); i++) {
        out<<i->first->getName()<<". "<<i->first<<" -> "<<"( ";
        for(auto j = i->second.begin(); j != i->second.end(); j++) {
            if(j != i->second.begin()) errs()<<", ";
            out<<(*j)->getName()<<". "<<(*j);
        }
        out<<" ) | ";
    }
    out<<"}";
    return out;
}
inline raw_ostream& operator<<(raw_ostream& out, const PointerInfo& pi) {
    out<<"\tps: "<<pi.ps<<" ";
    out<<"ps_field: "<<pi.ps_field<<"\n";
    return out;
}

class FuncPtrVisitor : public DataflowVisitor<struct PointerInfo> {
public:
    std::map<Function*, PointerInfo> arg_p2s;
    std::map<Function*, PointerInfo> ret_arg_p2s;
    std::map<Function*, std::set<Function*>> caller_map;
    std::map<Function*, std::set<Value*>> ret_p2s;
    std::map<int, std::list<Function*>> result;
    std::set<Function*> worklist;
    bool change = false;
    FuncPtrVisitor() : result(), arg_p2s(), ret_p2s(), ret_arg_p2s(), caller_map() {}
    void merge(PointerInfo* dest, const PointerInfo& src) override {
        for(Pointer2Set::const_iterator i=src.ps.begin(); i!=src.ps.end(); i++)
            for(std::set<Value*>::iterator j=i->second.begin(); j!=i->second.end(); j++) dest->ps[i->first].insert(*j);
        for(Pointer2Set::const_iterator i=src.ps_field.begin(); i!=src.ps_field.end(); i++)
            for(std::set<Value*>::iterator j = i->second.begin(); j != i->second.end(); j++) dest->ps_field[i->first].insert(*j);
    }

    void mergeInput(Function* fn, BasicBlock* bb, PointerInfo* bbinval) {
        PointerInfo pi = arg_p2s[fn];;
        for(auto i : pi.ps) {
            bbinval->ps[i.first].clear();
            bbinval->ps[i.first].insert(i.second.begin(), i.second.end());
        }
        for(auto i : pi.ps_field) {
            bbinval->ps_field[i.first].clear();
            bbinval->ps_field[i.first].insert(i.second.begin(), i.second.end());
        }
    }
    void handleCallInst(CallInst* callInst, PointerInfo* dfval) {
        std::map<Function*, PointerInfo> old_arg_p2s = arg_p2s;
        int line = callInst->getDebugLoc().getLine();
        result[line].clear();
        std::set<Function*> callees = getFuncByValue_work(callInst->getCalledOperand(), dfval);
        for(auto i=callees.begin(); i!=callees.end(); i++) callees.insert(*i);

        for(auto i = callees.begin(); i != callees.end(); i++) {
            result[line].push_back(*i);
            caller_map[*i].insert(callInst->getFunction());
        }
        PointerInfo caller_args;
        for(unsigned i=0; i<callInst->getNumArgOperands(); i++) {
            Value* arg = callInst->getArgOperand(i);
            if(arg->getType()->isPointerTy()) {
                if(Function* func = dyn_cast<Function>(arg)) {
                    caller_args.ps[arg].insert(func);
                } else {
                    caller_args.ps[arg].insert(dfval->ps[arg].begin(), dfval->ps[arg].end());
                    caller_args.ps_field[arg].insert(dfval->ps_field[arg].begin(), dfval->ps_field[arg].end());
                }
            }
        }
        if(caller_args.ps.empty()) return;
        std::map<Function*, std::map<Value*, Value*>> argmap;
        std::set<Value*> cr_arg_set;
        std::set<Value*> ce_arg_set;
        for(auto i=callees.begin(); i!=callees.end(); i++) {
            Function* callee = *i;
            for(unsigned j=0; j<callInst->getNumArgOperands(); j++) {
                Value* caller_arg = callInst->getArgOperand(j);
                if(caller_arg->getType()->isPointerTy()) {
                    Value* callee_arg = callee->arg_begin()+j;
                    cr_arg_set.insert(caller_arg);
                    ce_arg_set.insert(callee_arg);
                    argmap[callee][callee_arg] = caller_arg;
                    argmap[callee][caller_arg] = callee_arg;
                }
            }
        }
        for(auto i = callees.begin(); i != callees.end(); i++) {
            Function* callee = *i;
            for(unsigned j = 0; j < callInst->getNumArgOperands(); j++) {
                Value* caller_arg = callInst->getArgOperand(j);
                if(caller_arg->getType()->isPointerTy()) {
                    Value* callee_arg = callee->arg_begin() + j;
                    arg_p2s[callee].ps[callee_arg].insert(caller_args.ps[caller_arg].begin(), caller_args.ps[caller_arg].end());
                    arg_p2s[callee].ps_field[callee_arg].insert(caller_args.ps_field[caller_arg].begin(), caller_args.ps_field[caller_arg].end());
                    std::set<Value*> wl;
                    for(auto* k : caller_args.ps[caller_arg]) wl.insert(&*k);
                    for(auto* k : caller_args.ps_field[caller_arg]) wl.insert(&*k);
                    std::set<Value*> oldlist;
                    while (!wl.empty()) {
                        Value* v = *wl.begin();
                        wl.erase(wl.begin());
                        if(oldlist.count(v)) continue;
                        oldlist.insert(v);
                        arg_p2s[callee].ps[v].insert(dfval->ps[v].begin(), dfval->ps[v].end());
                        wl.insert(dfval->ps[v].begin(), dfval->ps[v].end());
                        arg_p2s[callee].ps_field[v].insert(dfval->ps_field[v].begin(), dfval->ps_field[v].end());
                        wl.insert(dfval->ps_field[v].begin(), dfval->ps_field[v].end());
                    }
                }
            }
        }
        for(auto i=callees.begin(); i!=callees.end(); i++) {
            Function* callee = *i;
            for(auto j : ret_arg_p2s[callee].ps) {
                Value* t = j.first;
                if(ce_arg_set.count(t) > 0) t = argmap[callee][t];
                dfval->ps[t].clear();
                for(auto k : j.second) {
                    if(ce_arg_set.count(&*k) > 0) dfval->ps[t].insert(argmap[callee][&*k]);
                    else dfval->ps[t].insert(&*k);
                }
            }
            for(auto j : ret_arg_p2s[callee].ps_field) {
                Value* t = j.first;
                if(ce_arg_set.count(t) > 0) t = argmap[callee][t];
                dfval->ps_field[t].clear();
                for(auto k : j.second) {
                    if(ce_arg_set.count(&*k) > 0) dfval->ps_field[t].insert(argmap[callee][&*k]);
                    else dfval->ps_field[t].insert(&*k);
                }
            }
        }
        for(auto i = callees.begin(); i != callees.end(); i++) if(!ret_p2s[*i].empty()) dfval->ps[callInst].insert(ret_p2s[*i].begin(), ret_p2s[*i].end());
        if(old_arg_p2s != arg_p2s) for(auto i = callees.begin(); i!=callees.end(); i++) worklist.insert(*i);
    }
    void compDFVal(Instruction* inst, PointerInfo* dfval) override {
        if(isa<DbgInfoIntrinsic>(inst)) return;
        if(isa<IntrinsicInst>(inst)) {
            if(MemCpyInst* memCpyInst = dyn_cast<MemCpyInst>(inst)) {
                if(!dyn_cast<BitCastInst>(memCpyInst->getArgOperand(0))) return;
                Value* dst = dyn_cast<BitCastInst>(memCpyInst->getArgOperand(0))->getOperand(0);
                if(!dyn_cast<BitCastInst>(memCpyInst->getArgOperand(1))) return;
                Value* src = dyn_cast<BitCastInst>(memCpyInst->getArgOperand(1))->getOperand(0);
                dfval->ps[dst].clear();
                dfval->ps[dst].insert(dfval->ps[src].begin(), dfval->ps[src].end());
                dfval->ps_field[dst].clear();
                dfval->ps_field[dst].insert(dfval->ps_field[src].begin(), dfval->ps_field[src].end());
            }
            return;
        }
        if(ReturnInst* returnInst = dyn_cast<ReturnInst>(inst)) {
            Function* func = returnInst->getFunction();
            Value* retValue = returnInst->getReturnValue();
            auto temp1 = ret_arg_p2s[func];
            for(auto i : arg_p2s[func].ps) {
                ret_arg_p2s[func].ps[i.first].clear();
                ret_arg_p2s[func].ps[i.first].insert(dfval->ps[i.first].begin(), dfval->ps[i.first].end());
            }
            for(auto i : arg_p2s[func].ps_field) {
                ret_arg_p2s[func].ps_field[i.first].clear();
                ret_arg_p2s[func].ps_field[i.first].insert(dfval->ps_field[i.first].begin(), dfval->ps_field[i.first].end());
            }
            bool flag = false;
            if(!(ret_arg_p2s[func] == temp1)) flag = true;
            if(retValue && retValue->getType()->isPointerTy()) {
                auto temp2 = ret_p2s[func];
                ret_p2s[func].insert(dfval->ps[retValue].begin(), dfval->ps[retValue].end());
                if(ret_p2s[func] != temp2) flag = true;
            }
            if(flag) {
                for(auto f : caller_map[func]) {
                    Function* ff = &*f;
                    worklist.insert(ff);
                }
            }
        } else if(LoadInst* loadInst = dyn_cast<LoadInst>(inst)) {
            Value* target_value = loadInst->getPointerOperand();
            dfval->ps[loadInst].clear();
            std::set<Value*> values;
            if(GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(target_value)) {
                Value* ptr = gepInst->getPointerOperand();
                values = dfval->ps[ptr];
                if(dfval->ps[ptr].empty()) {
                    values = dfval->ps_field[ptr];
                    dfval->ps[loadInst].insert(values.begin(), values.end());
                } else for(auto i=dfval->ps[ptr].begin(); i!=dfval->ps[ptr].end(); i++) dfval->ps[loadInst].insert(dfval->ps_field[*i].begin(), dfval->ps_field[*i].end());
            } else dfval->ps[loadInst].insert(dfval->ps[target_value].begin(), dfval->ps[target_value].end());
        } else if(PHINode* phyNode = dyn_cast<PHINode>(inst)) {
            dfval->ps[phyNode].clear();
            for(Value* v : phyNode->incoming_values()) {
                if(Function* func = dyn_cast<Function>(v)) {
                    dfval->ps[phyNode].insert(func);
                } else if(v->getType()->isPointerTy()) dfval->ps[phyNode].insert(dfval->ps[v].begin(), dfval->ps[v].end());
            }
        } else if(StoreInst* storeInst = dyn_cast<StoreInst>(inst)) {
            Value* store_value = storeInst->getValueOperand();
            Value* target_value = storeInst->getPointerOperand();
            std::set<Value*> store_values;
            if(dfval->ps[store_value].empty()) store_values.insert(store_value);
            else store_values.insert(dfval->ps[store_value].begin(), dfval->ps[store_value].end());
            if(GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(target_value)) {
                Value* ptr = gepInst->getPointerOperand();
                if(dfval->ps[ptr].empty()) {
                    dfval->ps_field[ptr].clear();
                    dfval->ps_field[ptr].insert(store_values.begin(), store_values.end());
                } else {
                    std::set<Value*> values = dfval->ps[ptr];
                    for(auto i=values.begin(); i!=values.end(); i++) {
                        dfval->ps_field[*i].clear();
                        dfval->ps_field[*i].insert(store_values.begin(), store_values.end());
                    }
                }
            } else{
                dfval->ps[target_value].clear();
                dfval->ps[target_value].insert(store_values.begin(), store_values.end());
            }
        } else if(GetElementPtrInst* getElementPtrInst = dyn_cast<GetElementPtrInst>(inst)) {
            Value* ptr = getElementPtrInst->getPointerOperand();
            dfval->ps[getElementPtrInst].clear();
            if(dfval->ps[ptr].empty()) dfval->ps[getElementPtrInst].insert(ptr);
            else dfval->ps[getElementPtrInst].insert(dfval->ps[ptr].begin(), dfval->ps[ptr].end());
        } else if(CallInst* callInst = dyn_cast<CallInst>(inst)) handleCallInst(callInst, dfval);
    }

    std::set<Function*> getFuncByValue_work(Value* value, PointerInfo* dfval) {
        std::set<Function*> res;
        if(Function* i = dyn_cast<Function>(value)) {
            res.insert(i);
            return res;
        }
        for(auto i = dfval->ps[value].begin(); i!=dfval->ps[value].end(); i++) {
            std::set<Function*> r = getFuncByValue_work(*i, dfval);
            res.insert(r.begin(), r.end());
        }
        return res;
    }
    void printResult() {
        for(std::map<int, std::list<Function*>>::iterator i=result.begin(); i!=result.end(); i++) {
            errs()<<i->first<<" : ";
            if(i->second.empty()) {
                errs()<<"\n";
                continue;
            }
            i->second.sort();
            i->second.unique();
            std::list<Function*>::iterator funcEnd = i->second.end();
            --funcEnd;
            for(std::list<Function*>::iterator j=i->second.begin(); j!=funcEnd; j++) errs()<<(*j)->getName()<<',';
            errs()<<(*funcEnd)->getName()<<'\n';
        }
    }
};