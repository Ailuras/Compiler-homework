#ifndef _DATAFLOW_H_
#define _DATAFLOW_H_
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <map>
using namespace llvm;

template <class T>
struct DataflowResult { typedef typename std::map<BasicBlock *, std::pair<T, T> > Type; };
template <class T>
struct DataflowInsResult { typedef typename std::map<Instruction *, std::pair<T, T> > Type; };
template <class T>
class DataflowVisitor {
public:
    virtual ~DataflowVisitor() {}
    virtual void compDFVal(BasicBlock *block, T *dfval, bool isforward) {
        if (isforward == true) for(BasicBlock::iterator i=block->begin(); i!=block->end(); i++) compDFVal(&*i, dfval);
        else for(BasicBlock::reverse_iterator i=block->rbegin(); i!=block->rend(); i++) compDFVal(&*i, dfval);
    }
    virtual void compDFVal(BasicBlock *block, typename DataflowInsResult<T>::Type *dfval, bool isforward) {
        if (isforward == true) for(BasicBlock::iterator i=block->begin(); i!=block->end(); i++) compDFVal(&*i, dfval);
        else for(BasicBlock::reverse_iterator i=block->rbegin(); i!=block->rend(); i++) compDFVal(&*i, dfval);
    }
    virtual void mergeInput(Function *func, BasicBlock *block, T *bbinval){};
    virtual void compDFVal(Instruction *inst, T *dfval){};
    virtual void compDFVal(Instruction *inst, typename DataflowInsResult<T>::Type *dfval){};
    virtual void merge(T *dest, const T &src) = 0;
};
Instruction *getFisrtIns(BasicBlock *block) {
    Instruction *ins = &*(block->begin());
    return ins;
}
Instruction *getLastIns(BasicBlock *block) {
    Instruction *ins = &*(--(block->end()));
    return ins;
}
template <class T>
void compForwardDataflow(Function *fn, DataflowVisitor<T> *visitor, typename DataflowResult<T>::Type *result, const T &initval) {
    std::set<BasicBlock *> worklist;
    for(Function::iterator i=fn->begin(); i!=fn->end(); i++) {
        worklist.insert(&*i);
        result->insert(std::make_pair(&*i, std::make_pair(initval, initval)));
    }
    while (!worklist.empty()) {
        BasicBlock *block = *worklist.begin();
        worklist.erase(worklist.begin());
        T bbinval = (*result)[block].first;
        if (block == &fn->getEntryBlock()) visitor->mergeInput(fn, block, &bbinval);
        else {
            bbinval.ps_field.clear();
            bbinval.ps.clear();
            for(auto i=pred_begin(block); i!=pred_end(block); i++) visitor->merge(&bbinval, (*result)[*i].second);
        }
        T old_bbexitval = (*result)[block].second;
        (*result)[block].first = bbinval;
        visitor->compDFVal(block, &bbinval, true);
        if (bbinval == (*result)[block].second) continue;
        (*result)[block].second = bbinval;
        for(succ_iterator i=succ_begin(block); i!=succ_end(block); i++) worklist.insert(*i);
    }
    return;
}
template <class T>
void compBackwardDataflow(Function *fn, DataflowVisitor<T> *visitor, typename DataflowResult<T>::Type *result, const T &initval) {
    std::set<BasicBlock *> worklist;
    for(Function::iterator bi = fn->begin(); bi != fn->end(); ++bi) {
        BasicBlock *bb = &*bi;
        result->insert(std::make_pair(bb, std::make_pair(initval, initval)));
        worklist.insert(bb);
    }
    while (!worklist.empty()) {
        BasicBlock *bb = *worklist.begin();
        worklist.erase(worklist.begin());
        T bbexitval = (*result)[bb].second;
        for(auto si = succ_begin(bb), se = succ_end(bb); si != se; si++) {
            BasicBlock *succ = *si;
            visitor->merge(&bbexitval, (*result)[succ].first);
        }
        (*result)[bb].second = bbexitval;
        visitor->compDFVal(bb, &bbexitval, false);
        if (bbexitval == (*result)[bb].first) continue;
        (*result)[bb].first = bbexitval;
        for(pred_iterator i=pred_begin(bb); i!=pred_end(bb); i++) worklist.insert(*i);
    }
}
template <class T>
void printDataflowResult(raw_ostream &out, const typename DataflowResult<T>::Type &dfresult) {
    for(typename DataflowResult<T>::Type::const_iterator i=dfresult.begin(); i!=dfresult.end(); i++) {
        if(i->first == NULL) out<<"*";
        else i->first->dump();
        out<<"\n\tin : "<<i->second.first<<"\n\tout :  "<<i->second.second<<"\n";
    }
}
#endif /* !_DATAFLOW_H_ */