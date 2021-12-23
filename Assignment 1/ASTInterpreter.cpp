//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool
//--------------===//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/EvaluatedExprVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

#include "Environment.h"

class InterpreterVisitor : public EvaluatedExprVisitor<InterpreterVisitor> {
private:
    Environment *mEnv;

public:
    explicit InterpreterVisitor(const ASTContext &context, Environment *env) : EvaluatedExprVisitor(context), mEnv(env) {}
    virtual ~InterpreterVisitor() {}

    bool visit(Expr *condition) { Visit(condition); return true; }
    bool isDone() { return mEnv->isCurFuncReturned(); }
    //访问圆括号语句
    virtual void VisitParenExpr(ParenExpr *pexpr) {
        if(isDone()) return;
        VisitStmt(pexpr);
        mEnv->parenexpr(pexpr);
    }
    //访问一元操作符 -a
    virtual void VisitUnaryOperator(UnaryOperator *uop) {
        if(isDone()) return;
        VisitStmt(uop);
        mEnv->unaryop(uop);
    }
    //访问二元操作符 a > b
    virtual void VisitBinaryOperator(BinaryOperator *bop) {
        if(isDone()) return;
        VisitStmt(bop);
        mEnv->binop(bop);
    }
    //声明再次调用 int a then a = 1的a
    virtual void VisitDeclRefExpr(DeclRefExpr *expr) {
        if(isDone()) return;
        VisitStmt(expr);
        mEnv->declref(expr);
    }
    virtual void VisitCastExpr(CastExpr *expr) {
        if(isDone()) return;
        VisitStmt(expr);
        mEnv->cast(expr);
    }
    //访问数组
    virtual void VisitArraySubscriptExpr(ArraySubscriptExpr *expr) {
        if(isDone()) return;
        Visit(expr->getLHS());
        Visit(expr->getRHS());
        mEnv->arrayref(expr);
    }
    //访问返回语句 exp: return 0;
    virtual void VisitReturnStmt(ReturnStmt *rets) {
        if(isDone()) return;
        Visit(rets->getRetValue());
        mEnv->retstmt(rets);
    }
    //访问调用语句
    virtual void VisitCallExpr(CallExpr *call) {
        if(isDone()) return;
        VisitStmt(call);
        mEnv->call(call);
        FunctionDecl *callee = call->getCalleeDecl()->getAsFunction();
        if(mEnv->isExternalCall(callee)) return; //当call为外部调用时
        if(callee->hasBody()) VisitStmt(callee->getBody());
        mEnv->ret(call); //调用结束后调用返回函数，释放临时栈，返回值
    }
    //访问赋值语句, exp:a = 1
    virtual void VisitDeclStmt(DeclStmt *declstmt) {
        if(isDone()) return;
        VisitStmt(declstmt);
        mEnv->decl(declstmt);
    }
    //访问while语句
    virtual void VisitWhileStmt(WhileStmt *whilestmt) {
        if(isDone()) return;
        Expr *condition = whilestmt->getCond(); //获取while的条件语句
        while (visit(condition) && mEnv->expr(condition)) {
            Visit(whilestmt->getBody());
            if(isDone()) return;
        }
    }
    //访问for循环语句
    virtual void VisitForStmt(ForStmt *forstmt) {
        if(isDone()) return;
        Stmt *initstmt = forstmt->getInit(), *body = forstmt->getBody(); //for的初始化和主体
        Expr *condition = forstmt->getCond(), *inc = forstmt->getInc(); //for的条件和自增
        if(initstmt) VisitStmt(initstmt);
        bool flag = condition ? false : true;
        while(flag || (visit(condition) && mEnv->expr(condition))) {
            Visit(body); Visit(inc);//先主体部分，后inc
            if(isDone()) return;
        }
    }
    //访问if语句
    virtual void VisitIfStmt(IfStmt *ifstmt) {
        if(isDone()) return;
        Expr *condition = ifstmt->getCond();
        if(visit(condition) && mEnv->expr(condition)) Visit(ifstmt->getThen());
        else if(ifstmt->getElse()) Visit(ifstmt->getElse()); //访问false分支
    }
    virtual void VisitUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr *tte) {
        if(isDone()) return;
        VisitStmt(tte);
        if(tte->getKind() == UETT_SizeOf) mEnv->sizeofexpr(tte);
    }
    //访问整数型常量
    virtual void VisitIntegerLiteral(IntegerLiteral *il) {
        if(isDone()) return;
        mEnv->integerLiteral(il);
    }
    //访问字符型常量
    virtual void VisitCharacterLiteral(CharacterLiteral *cl) {
        if(isDone()) return;
        mEnv->characterLiteral(cl);
    }
};

class InterpreterConsumer : public ASTConsumer {
private:
    Environment mEnv; //环境类
    InterpreterVisitor mVisitor; //AST遍历器

public:
    explicit InterpreterConsumer(const ASTContext &context) : mEnv(), mVisitor(context, &mEnv) {}
    virtual ~InterpreterConsumer() {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        mEnv.init(Context.getTranslationUnitDecl()); //以根节点为参数传入mEnv
        mVisitor.VisitStmt(mEnv.getEntry()->getBody()); //开始遍历main函数中的语句
    }
};

class InterpreterClassAction : public ASTFrontendAction {
public:
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        return std::unique_ptr<clang::ASTConsumer>(new InterpreterConsumer(Compiler.getASTContext()));
    }
};

int main(int argc, char **argv) {
    if(argc > 1) {
        clang::tooling::runToolOnCode( std::unique_ptr<clang::FrontendAction>(new InterpreterClassAction), argv[1]);
    }
}