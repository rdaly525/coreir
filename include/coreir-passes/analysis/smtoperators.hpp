#ifndef SMTOPERATORS_HPP_
#define SMTOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {
    typedef std::pair<string, SmtBVVar> named_var;
    
    string SmtBVVarDec(SmtBVVar w);
    string SMTgetCurr(string var);
    string SMTgetNext(string var);
    SmtBVVar SmtBVVarGetInit(SmtBVVar var);
    SmtBVVar SmtBVVarGetNext(SmtBVVar var);
    SmtBVVar SmtBVVarGetCurr(SmtBVVar var);
    string getSMTbits(unsigned, int);
    string SMTAssign(SmtBVVar vleft, SmtBVVar vright);
    string SMTAnd(string context, SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTOr(string context, SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTNot(string context, SmtBVVar in, SmtBVVar out);
    string SMTConst(string context, SmtBVVar out, string val);
    string SMTAdd(string context, SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTConcat(string context, SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
    string SMTReg(string context, SmtBVVar in, SmtBVVar clk, SmtBVVar out);
    string SMTRegPE(string context, SmtBVVar in, SmtBVVar clk, SmtBVVar out, SmtBVVar en);
    string SMTCounter(string context, SmtBVVar clk, SmtBVVar en, SmtBVVar out);
    string SMTSlice(string context, SmtBVVar in, SmtBVVar out, string low, string high);
    string SMTClock(string context, SmtBVVar clk_p);
  }
}
#endif
