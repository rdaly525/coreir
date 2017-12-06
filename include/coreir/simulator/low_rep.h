#pragma once

#include <cassert>
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
    virtual std::string cString() const = 0;

    virtual ~LowExpr() {}
  };

  class LowId : public LowExpr {
    std::string name;

  public:
    LowId(const std::string& name_) : name(name_) {}

    virtual std::string cString() const;
  };

  class LowBitVec : public LowExpr {
  public:
    virtual std::string cString() const { assert(false); }
  };

  class LowUnop : public LowExpr {
  public:
    virtual std::string cString() const { assert(false); }

  };

  class LowBinop : public LowExpr {
  public:
    virtual std::string cString() const { assert(false); }

  };

  enum LowStmtType {
    LOW_STMT_ASSIGN,
  };

  class LowStmt {
  public:

    virtual std::string cString() const = 0;
    virtual LowStmtType getType() const = 0;

    virtual ~LowStmt() {}
  };

  class LowAssign : public LowStmt {
    LowExpr* lhs;
    LowExpr* rhs;

  public:
    LowAssign(LowExpr* const lhs_,
              LowExpr* const rhs_) : lhs(lhs_), rhs(rhs_) {}

    LowExpr* getLHS() const { return lhs; }
    LowExpr* getRHS() const { return rhs; }

    virtual LowStmtType getType() const { return LOW_STMT_ASSIGN; }

    virtual std::string cString() const {
      return getLHS()->cString() + " = " + getRHS()->cString() + ";\n";
    }
  };

  class LowProgram {
  protected:
    std::vector<LowStmt*> stmts;
    std::vector<LowExpr*> exprs;

  public:


    std::string cString() const;

    void addAssignStmt(LowExpr* const lhs,
                       LowExpr* const rhs) {
      stmts.push_back(new LowAssign(lhs, rhs));
      exprs.push_back(lhs);
      exprs.push_back(rhs);
    }

    ~LowProgram() {
      for (auto& stmt : stmts) {
        delete stmt;
      }

      for (auto& expr : exprs) {
        delete expr;
      }

    }
  };

}
