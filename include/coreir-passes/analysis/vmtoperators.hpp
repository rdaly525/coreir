#ifndef VMTOPERATORS_HPP_
#define VMTOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/vmtmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {
    typedef std::pair<string, VmtBVVar> named_var;
    
    string VmtBVVarDec(VmtBVVar w);
    string VMTgetCurr(string var);
    string VMTgetNext(string var);
    VmtBVVar VmtBVVarGetInit(VmtBVVar var);    
    VmtBVVar VmtBVVarGetNext(VmtBVVar var);    
    VmtBVVar VmtBVVarGetCurr(VmtBVVar var);    
    string getVMTbits(unsigned, int);
    string VMTAssign(VmtBVVar vleft, VmtBVVar vright);
    string VMTAnd(named_var in1, named_var in2, named_var out);
    string VMTOr(named_var in1, named_var in2, named_var out);
    string VMTNot(named_var in, named_var out);
    string VMTConst(named_var out, string val);
    string VMTAdd(named_var in1, named_var in2, named_var out);
    string VMTConcat(named_var in1, named_var in2, named_var out);
    string VMTReg(named_var in, named_var clk, named_var out);    
    string VMTRegPE(named_var in, named_var clk, named_var out, named_var en);
    string VMTCounter(named_var clk, named_var en, named_var out);
    string VMTSlice(named_var in, named_var out, string low, string high);
    string VMTClock(named_var clk_p);
  }
}
#endif
