#ifndef SMVOPERATORS_HPP_
#define SMVOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/smvmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {
    typedef std::pair<string, SmvBVVar> named_var;
    
    string SmvBVVarDec(SmvBVVar w);
    string SMVgetCurr(string var);
    string SMVgetNext(string var);
    SmvBVVar SmvBVVarGetInit(SmvBVVar var);
    SmvBVVar SmvBVVarGetNext(SmvBVVar var);
    SmvBVVar SmvBVVarGetCurr(SmvBVVar var);
    string getSMVbits(unsigned, int);
    string SMVAssign(SmvBVVar vleft, SmvBVVar vright);
    string SMVAnd(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVOr(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVNot(string context, SmvBVVar in, SmvBVVar out);
    string SMVConst(string context, SmvBVVar out, string val);
    string SMVAdd(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVConcat(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVReg(string context, SmvBVVar in, SmvBVVar clk, SmvBVVar out);
    string SMVRegPE(string context, SmvBVVar in, SmvBVVar clk, SmvBVVar out, SmvBVVar en);
    string SMVCounter(string context, SmvBVVar clk, SmvBVVar en, SmvBVVar out);
    string SMVSlice(string context, SmvBVVar in, SmvBVVar out, string low, string high);
    string SMVClock(string context, SmvBVVar clk_p);
  }
}
#endif
