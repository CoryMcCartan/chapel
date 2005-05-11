#include "transformLetExprs.h"
#include "expr.h"
#include "stmt.h"
#include "symbol.h"
#include "type.h"
#include "symtab.h"
#include "stringutil.h"
#include "insertFunctionTemps.h"


TransformLetExprs::TransformLetExprs() {
  lets.clear();
}


void TransformLetExprs::postProcessExpr(Expr* expr) {
  if (LetExpr* letExpr = dynamic_cast<LetExpr*>(expr)) {
    lets.add(letExpr);
  }
}


void TransformLetExprs::run(ModuleSymbol* moduleList) {
  Traversal::run(moduleList);
  doTransformation();
}


void TransformLetExprs::doTransformation(void) {
  static int uid = 1;
  forv_Vec(BaseAST, ast, lets) {
    LetExpr* letExpr = dynamic_cast<LetExpr*>(ast);
    if (!letExpr) {
      INT_FATAL(ast, "LetExpr expected");
    }
    Stmt* letStmt = letExpr->getStmt();
    BlockStmt* blockStmt = Symboltable::startCompoundStmt();
    Expr* innerCopy = letExpr->innerExpr->copy(false, NULL, NULL, &lets);
    letExpr->replace(innerCopy);
    Map<BaseAST*,BaseAST*>* map = new Map<BaseAST*,BaseAST*>();
    DefExpr* defExpr =
      dynamic_cast<DefExpr*>(letExpr->symDefs->copyList(true, map, NULL, &lets));
    Stmt* letStmtCopy = letStmt->copy(false, map, NULL, &lets);
    DefStmt* defStmt = new DefStmt(defExpr);
    defStmt->append(letStmtCopy);
    blockStmt = Symboltable::finishCompoundStmt(blockStmt, defStmt);

    for (DefExpr* tmp = defExpr; tmp; tmp = nextLink(DefExpr, tmp)) {
      tmp->sym->cname =
        glomstrings(3, tmp->sym->cname, "_let_", intstring(uid++));
    }

    letStmt->replace(blockStmt);
    TRAVERSE(blockStmt, new InsertFunctionTemps(), true);
  }
}
