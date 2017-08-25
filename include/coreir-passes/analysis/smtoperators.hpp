#ifndef SMTOPERATORS_HPP_
#define SMTOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {
    
    string SmtBVVarDec(SmtBVVar w);
    string SMTgetCurr(string var);
    string SMTgetNext(string var);
    SmtBVVar SmtBVVarGetNext(SmtBVVar var);    
    SmtBVVar SmtBVVarGetCurr(SmtBVVar var);    
    string getSMTbits(unsigned, int);
    string SMTAssign(SmtBVVar vleft, SmtBVVar vright);
    string SMTAnd(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTOr(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTNot(SmtBVVar in, SmtBVVar out);
    string SMTConst(SmtBVVar out, string val);
    string SMTAdd(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTConcat(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTReg(SmtBVVar in, SmtBVVar clk, SmtBVVar out);    
    string SMTRegPE(SmtBVVar in, SmtBVVar clk, SmtBVVar out, SmtBVVar en);
    string SMTCounter(SmtBVVar clk, SmtBVVar en, SmtBVVar out);
    string SMTSlice(SmtBVVar in, SmtBVVar out, string low, string high);
    string SMTClock(SmtBVVar clk_p);
  }
}
#endif
