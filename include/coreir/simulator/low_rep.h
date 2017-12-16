#pragma once

#include <cassert>
#include <string>
#include <vector>

#include "coreir/ir/dynamic_bit_vector.h"
#include "coreir/ir/fwd_declare.h"
#include "coreir/simulator/print_c.h"

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
    BitVector bv;

  public:
    LowBitVec(const BitVector& bv_) : bv(bv_) {}
    virtual std::string cString() const {
      std::stringstream ss;
      ss << "0b" << bv;
      return ss.str();
    }
    //assert(false); }
  };

  class LowUnop : public LowExpr {
    std::string op;
    LowExpr* op0;

  public:

    LowUnop(const std::string& op_,
            LowExpr* const op0_) : op(op_), op0(op0_) {}

    virtual std::string cString() const {
      if (op == "ULL") {
        return parens(parens(op0->cString()) + op);
      }
      return parens(op + op0->cString());
    }

    virtual ~LowUnop() {
      delete op0;
    }
  };

  class LowBinop : public LowExpr {
    std::string op;
    LowExpr* op0;
    LowExpr* op1;

  public:
    LowBinop(const std::string& op_,
             LowExpr* const op0_,
             LowExpr* const op1_) : op(op_), op0(op0_), op1(op1_) {}

    virtual std::string cString() const {
      if (op == "MASK") {
        return op + parens(op0->cString() + ", " + op1->cString());
      }
      return parens(op0->cString() + " " + op + " " + op1->cString());
    }

    virtual ~LowBinop() {
      delete op0;
      delete op1;
    }
    
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

    virtual ~LowAssign() {
      delete lhs;
      delete rhs;
    }
  };

  class LowProgram {
  protected:
    std::vector<LowStmt*> stmts;
    //std::vector<LowExpr*> exprs;

  public:


    std::string cString() const;

    void addAssignStmt(LowExpr* const lhs,
                       LowExpr* const rhs) {
      stmts.push_back(new LowAssign(lhs, rhs));
      // exprs.push_back(lhs);
      // exprs.push_back(rhs);
    }

    ~LowProgram() {
      for (auto& stmt : stmts) {
        delete stmt;
      }

      // for (auto& expr : exprs) {
      //   delete expr;
      // }

    }
  };

}
