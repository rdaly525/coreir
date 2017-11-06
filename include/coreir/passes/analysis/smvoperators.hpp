#ifndef SMVOPERATORS_HPP_
#define SMVOPERATORS_HPP_

#include "coreir.h"
#include "coreir/passes/analysis/smvmodule.hpp"
#include <ostream>

using namespace CoreIR;
using namespace std;
namespace CoreIR {
  namespace Passes {
    typedef std::pair<string, SmvBVVar> named_var;
    typedef enum e_PropType
      {
        invarspec,
        ltlspec
      } PropType;

    typedef pair<PropType, string> PropDef;
    
    string SmvBVVarDec(SmvBVVar w);
    string SMVgetCurr(string var);
    string SMVgetNext(string var);
    SmvBVVar SmvBVVarGetNext(SmvBVVar var);
    SmvBVVar SmvBVVarGetCurr(SmvBVVar var);
    string getSMVbits(unsigned, int);
    string SMVAssign(SmvBVVar vleft, SmvBVVar vright);
    string SMVAnd(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVOr(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVXor(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVNot(string context, SmvBVVar in, SmvBVVar out);
    string SMVConst(string context, SmvBVVar out_p, int val);
    string SMVAdd(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVSub(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVConcat(string context, SmvBVVar in1, SmvBVVar in2, SmvBVVar out);
    string SMVReg(string context, SmvBVVar in, SmvBVVar clk, SmvBVVar out);
    string SMVRegPE(string context, SmvBVVar in, SmvBVVar clk, SmvBVVar out, SmvBVVar en);
    string SMVSlice(string context, SmvBVVar in, SmvBVVar out, int low, int high);
    string SMVClock(string context, SmvBVVar clk_p);
    string SMVMux(string context, SmvBVVar in0_p, SmvBVVar in1_p, SmvBVVar sel_p, SmvBVVar out_p);

    string SMVProperty(string name, PropType type, string value);
  }
}
#endif
