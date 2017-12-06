#pragma once

#include <string>
#include <vector>

namespace CoreIR {

  enum LowExprType {
    LOW_EXPR_ID,
    LOW_EXPR_UNOP,
    LOW_EXPR_BINOP,
    LOW_EXPR_BITVEC
  };

  class LowExpr {
  public:
  };

  class LowId : public LowExpr {
  };

  class LowBitVec : public LowExpr {
  };

  class LowUnop : public LowExpr {
  };

  class LowBinop : public LowExpr {
  };

  enum LowStmtType {
    LOW_STMT_ASSIGN,
  };

  class LowStmt {
  public:
  };

  class LowProgram {
  protected:
    std::vector<LowStmt*> stmts;

  public:

    ~LowProgram() {
      for (auto& stmt : stmts) {
        delete stmt;
      }
    }
  };

}
