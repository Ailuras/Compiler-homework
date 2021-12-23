//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool
//--------------===//
//===----------------------------------------------------------------------===//
#include <stdio.h>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

//栈，存储声明和语句，以及当前语句的相关信息
class StackFrame {
    /// StackFrame maps Variable Declaration to Value
    /// Which are either integer or addresses (also represented using an Integer value)
    std::map<Decl *, long> mVars; //存储声明
    std::map<Stmt *, long> mExprs; //存储计算语句的值，也包括常数
    Stmt *mPC; //当前语句
    long retValue = 0; //返回地址
    bool returned = false; //是否返回

public:
    StackFrame() : mVars(), mExprs(), mPC() {} //构造函数，初始化成员参数
    //约束声明decl的值为val
    void bindDecl(Decl *decl, long val) { mVars[decl] = val; }
    //返回声明decl的值
    long getDeclVal(Decl *decl) {
        assert(mVars.find(decl) != mVars.end());
        return mVars.find(decl)->second;
    }
    bool findDecl(Decl *decl) { return mVars.find(decl) != mVars.end(); }
    //关于mExprs
    //约束语句stmt的值为val
    void bindStmt(Stmt *stmt, long val) { mExprs[stmt] = val; }
    //返回stmt的值，包含<stmt, val>
    long getStmtVal(Stmt *stmt) {
        assert(mExprs.find(stmt) != mExprs.end());
        return mExprs[stmt];
    }
    void setPC(Stmt *stmt) { mPC = stmt; }
    Stmt *getPC() { return mPC; }
    long getRetValue() { return retValue; }
    void setRetValue(long value) { retValue = value; }
    void setReturned() { returned = true; }
    bool isReturned() { return returned; }
};

//堆，存储了常用的调用函数
class Heap {
    std::map<long *, int> block; //存储已经申请空间的数据块，左为地址，右为大小size
public:
    long *Malloc(int size) {
        long *addr = (long *)malloc(size);
        block[addr] = size;
        return addr;
    }
    void Free(long *addr) { if(block.find(addr) != block.end()) free(addr); }
    void Update(long *addr, long val) { for(auto &i : block) if((long)addr >= (long)(i.first) && (long)addr <= (long)(i.first+i.second)) *addr = val; }
    long Get(long *addr) {
        for(auto &i : block) if((long)addr >= (long)(i.first) && (long)addr <= (long)(i.first+i.second)) return *addr;
        return -1;
    }
};

//环境类，包含各种操作的实现
class Environment {
    std::vector<StackFrame> mStack; //栈
    Heap *mHeap; //堆
    FunctionDecl *mFree;  /// Declartions to the built-in functions
    FunctionDecl *mMalloc;
    FunctionDecl *mInput;
    FunctionDecl *mOutput;
    FunctionDecl *mEntry;

public:
    Environment() : mStack(), mFree(NULL), mMalloc(NULL), mInput(NULL), mOutput(NULL), mEntry(NULL) {}
    void init(TranslationUnitDecl *unit) {
        mHeap = new Heap(); //新建一个堆为mHeap
        mStack.push_back(StackFrame()); //用于保存全局变量
        for(TranslationUnitDecl::decl_iterator i = unit->decls_begin(), e = unit->decls_end(); i != e; ++i) {
            if(VarDecl *vdecl = dyn_cast<VarDecl>(*i)) vardecl(vdecl, &(mStack.back())); //处理全局var声明
            else if(FunctionDecl *fdecl = dyn_cast<FunctionDecl>(*i)) { //处理外部方法声明
                if(fdecl->getName().equals("FREE")) mFree = fdecl;
                else if(fdecl->getName().equals("MALLOC")) mMalloc = fdecl;
                else if(fdecl->getName().equals("GET")) mInput = fdecl;
                else if(fdecl->getName().equals("PRINT")) mOutput = fdecl;
                else if(fdecl->getName().equals("main")) { //函数名为main的是入口函数
                    mEntry = fdecl; 
                    mStack.push_back(StackFrame());
                }
            }
        }
    }
    FunctionDecl *getEntry() { return mEntry; }
    bool isExternalCall(FunctionDecl *f) { return f == mFree || f == mMalloc || f == mInput || f == mOutput; }
    bool isCurFuncReturned() { return mStack.back().isReturned(); }
    void sizeofexpr(UnaryExprOrTypeTraitExpr *tte) { mStack.back().bindStmt(tte, sizeof(long)); }
    void decl(DeclStmt *ds) { for(DeclStmt::decl_iterator it = ds->decl_begin(), ie = ds->decl_end(); it != ie; ++it) if(VarDecl *vdecl = dyn_cast<VarDecl>(*it)) vardecl(vdecl, &(mStack.back()));}
    // 对语句分情况进行操作
    long expr(Expr *exp) {
        Expr *e = exp->IgnoreImpCasts(); //忽略隐性类型转化
        if(BinaryOperator *bop = dyn_cast<BinaryOperator>(e)) { //二元运算符
            binop(bop); //对bop进行操作
            return mStack.back().getStmtVal(bop); //返回bop指向的值
        } else if(IntegerLiteral *i = dyn_cast<IntegerLiteral>(e)) { //整数型常量
            return (long)i->getValue().getSExtValue();
        } else if(CharacterLiteral *i = dyn_cast<CharacterLiteral>(e)) { //字符型常量
            return i->getValue();
        } else if(DeclRefExpr *i = dyn_cast<DeclRefExpr>(e)) { //引用已有变量
            declref(i);
            return mStack.back().getStmtVal(i);
        } else if(CallExpr *i = dyn_cast<CallExpr>(e)) { //调用语句
            return mStack.back().getStmtVal(i);
        } else if(UnaryOperator *i = dyn_cast<UnaryOperator>(e)) { //一元运算符
            return mStack.back().getStmtVal(i);
        } else if(ParenExpr *i = dyn_cast<ParenExpr>(e)) { //圆括号表达式
            return mStack.back().getStmtVal(i);
        } else if(ArraySubscriptExpr *i = dyn_cast<ArraySubscriptExpr>(e)) { //数组元素
            return mStack.back().getStmtVal(i);
        } else if(UnaryExprOrTypeTraitExpr *i = dyn_cast<UnaryExprOrTypeTraitExpr>(e)) {
            return mStack.back().getStmtVal(i);
        } else if(CStyleCastExpr *i = dyn_cast<CStyleCastExpr>(e)) {
            return expr(i->getSubExpr());
        } else return -1;
    }
    void parenexpr(ParenExpr *pe) {
        Expr *e = pe->getSubExpr(); //得到子树？
        long value = expr(e); //返回的是当前stack中mExprs中的expr e
        mStack.back().bindStmt(pe, value);
    }
    void assignment(Expr *left, Expr *right) {
        long leftval, rightval = expr(right);
        if(DeclRefExpr *i = dyn_cast<DeclRefExpr>(left)) { //变量赋值
            mStack.back().bindStmt(left, rightval);
            Decl *decl = i->getFoundDecl(); //得到left表示的变量的地址
            if(mStack.back().findDecl(decl)) mStack.back().bindDecl(decl, rightval); //修改局部变量
            else mStack.front().bindDecl(decl, rightval); //修改全局变量
        } else if(ArraySubscriptExpr *i = dyn_cast<ArraySubscriptExpr>(left)) { //数组赋值
            long leftval = expr(i->getIdx());
            DeclRefExpr *declref = dyn_cast<DeclRefExpr>(i->getLHS()->IgnoreImpCasts());
            Decl *decl = declref->getFoundDecl();
            long *arr = (long *)(mStack.back().findDecl(decl) ? mStack.back().getDeclVal(decl):mStack.front().getDeclVal(decl));
            arr[leftval] = rightval;
        } else if(UnaryOperator *i = dyn_cast<UnaryOperator>(left)) { //一元运算符
            leftval = expr(i->getSubExpr());
            mHeap->Update((long *)leftval, rightval);
        }
    }
    // 二元运算符分情况讨论 ok
    void binop(BinaryOperator *bop) {
        Expr *left = bop->getLHS(); //左语句
        Expr *right = bop->getRHS(); //右语句
        long leftval, rightval = expr(right);
        if(bop->isAssignmentOp()) {
            assignment(left, right);
        } else {
            leftval = expr(left);
            if(bop->isComparisonOp()) {
                switch (bop->getOpcode()) {
                    case BO_GT: mStack.back().bindStmt(bop, (leftval > rightval)); break;
                    case BO_LT: mStack.back().bindStmt(bop, (leftval < rightval)); break;
                    case BO_EQ: mStack.back().bindStmt(bop, (leftval == rightval)); break;
                    case BO_GE: mStack.back().bindStmt(bop, (leftval >= rightval)); break;
                    case BO_LE: mStack.back().bindStmt(bop, (leftval <= rightval)); break;
                    case BO_NE: mStack.back().bindStmt(bop, (leftval != rightval)); break;
                }
            } else if(bop->isAdditiveOp()) {  // 加号和减号操作符
                rightval *= (left->getType().getTypePtr()->isPointerType() && !right->getType().getTypePtr()->isPointerType()) ? sizeof(long):1;
                if(bop->getOpcode() == BO_Add) mStack.back().bindStmt(bop, leftval+rightval);
                else mStack.back().bindStmt(bop, leftval-rightval);
            } else if(bop->isMultiplicativeOp()) {  // 乘法和除法操作符
                if(bop->getOpcode() == BO_Mul) mStack.back().bindStmt(bop, leftval*rightval);
                else mStack.back().bindStmt(bop, leftval/rightval);
            }
        }
    }
    // 一元运算符分情况讨论
    void unaryop(UnaryOperator *uop) {
        Expr *e = uop->getSubExpr();
        long value = expr(e);
        if(uop->getOpcode() == UO_Plus) {
            mStack.back().bindStmt(uop, value);
        } else if(uop->getOpcode() == UO_Minus) {
            mStack.back().bindStmt(uop, -value);
        } else if(uop->getOpcode() == UO_Deref) {
            mStack.back().bindStmt(uop, mHeap->Get((long *)value));
        }
    }
    void callFunction(CallExpr *callexpr) {
        StackFrame current = StackFrame();
        for(int i = 0; i < callexpr->getDirectCallee()->getNumParams(); i++) { //？不知道行不行
            long val = expr(callexpr->getArg(i));
            VarDecl *addr = dyn_cast<VarDecl>(callexpr->getDirectCallee()->getParamDecl(i));
            vardecl(addr, &current);
            current.bindDecl(addr, val);
        }
        mStack.push_back(current);
    }
    void call(CallExpr *callexpr) {
        mStack.back().setPC(callexpr);
        long val = 0;
        FunctionDecl *callee = callexpr->getDirectCallee();
        if(!isExternalCall(callee)) callFunction(callexpr);
        else{
            if(callee == mInput) { //输入
                llvm::errs() << "Please Input an Integer Value : ";
                scanf("%ld", &val);
                mStack.back().bindStmt(callexpr, val);
            } else if(callee == mOutput) { //输出
                val = expr(callexpr->getArg(0));
                llvm::errs() << val;
            } else if(callee == mMalloc) { //内存申请
                val = expr(callexpr->getArg(0));
                mStack.back().bindStmt(callexpr, (long)mHeap->Malloc(val));
            } else if(callee == mFree) { //内存释放
                val = expr(callexpr->getArg(0));
                mHeap->Free((long *)val);
            }
        }
    }
    //返回语句
    void ret(CallExpr *callexpr) {
        FunctionDecl *callee = callexpr->getDirectCallee(); //getDirectCallee？
        if(!callee->isNoReturn()){
            long ret = mStack.back().getRetValue();
            mStack.pop_back();
            mStack.back().bindStmt(callexpr, ret); //将callexpr的值赋为rval
        } else mStack.pop_back();
    }
    void retstmt(ReturnStmt *rstmt) {
        if(rstmt->getRetValue()) mStack.back().setRetValue(expr(rstmt->getRetValue())); //将rval存为RetValue
        mStack.back().setReturned(); //将returned设为true、
    }
    void vardecl(VarDecl *vd, StackFrame *sf) {
        if(vd->getType().getTypePtr()->isIntegerType() || vd->getType().getTypePtr()->isCharType()) { //vdecl类型为整数型或字符型
            long value = vd->hasInit() ? expr(vd->getInit()) : 0;
            sf->bindDecl(vd, value); //将value存到vdecl中
        } else if(vd->getType().getTypePtr()->isArrayType()) { //vdecl为数组类型
            const ConstantArrayType *arr_type = dyn_cast<ConstantArrayType>(vd->getType().getTypePtr());
            int arr_size = arr_type->getSize().getSExtValue();
            assert(arr_size >= 0);
            if(arr_type->getElementType().getTypePtr()->isIntegerType()) sf->bindDecl(vd, (long)(new long[arr_size]));
            else if(arr_type->getElementType().getTypePtr()->isPointerType()) sf->bindDecl(vd, (long)(new long *[arr_size]));
        } else if(vd->getType().getTypePtr()->isPointerType()) {
            long value = vd->hasInit() ? expr(vd->getInit()) : 0;
            sf->bindDecl(vd, value);
        } else sf->bindDecl(vd, 0);
    }
    void declref(DeclRefExpr *declref) {
        mStack.back().setPC(declref);
        if(declref->getType()->isIntegerType() || declref->getType()->isPointerType()) { //declref为整数型或指针类型
            Decl *decl = declref->getFoundDecl();
            long val = mStack.back().findDecl(decl) ? mStack.back().getDeclVal(decl) : mStack.front().getDeclVal(decl);
            mStack.back().bindStmt(declref, val);
        }
    }
    void arrayref(ArraySubscriptExpr *aexpr) {
        long index = expr(aexpr->getIdx());
        DeclRefExpr *declref = dyn_cast<DeclRefExpr>(aexpr->getLHS()->IgnoreImpCasts()); //判断declref是否为声明引用
        assert(declref);
        Decl *decl = declref->getFoundDecl();
        long *arr = (long *)(mStack.back().findDecl(decl) ? mStack.back().getDeclVal(decl) : mStack.front().getDeclVal(decl));
        mStack.back().bindStmt(aexpr, arr[index]);
    }
    //类型转化
    void cast(CastExpr *castexpr) {
        mStack.back().setPC(castexpr);
        if(castexpr->getType()->isIntegerType()) {
            Expr *expr = castexpr->getSubExpr();
            long val = mStack.back().getStmtVal(expr); //得到expr的值
            mStack.back().bindStmt(castexpr, val); //然后赋给castexpr
        } else if(castexpr->getType()->isPointerType()) {}
    }
    //常量声明
    void integerLiteral(IntegerLiteral *ll) {
        long value = (long)ll->getValue().getLimitedValue(); //得到文字literal中的value
        mStack.back().bindStmt(ll, value); //将语句literal的值赋为value
    }
    void characterLiteral(CharacterLiteral *cl) {
        long value = (long)cl->getValue();
        mStack.back().bindStmt(cl, value);
    }
};