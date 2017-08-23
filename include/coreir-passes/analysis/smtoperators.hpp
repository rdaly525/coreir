#ifndef SMTOPERATORS_HPP_
#define SMTOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {
    typedef std::pair<string, SmtBVVar> named_var;
    
    string SMTgetNext(string var);
    string getSMTbits(unsigned, int);
    string SMTAssign(Connection con);
    string SMTAnd(named_var in1, named_var in2, named_var out);
    string SMTOr(named_var in1, named_var in2, named_var out);
    string SMTNot(named_var in, named_var out);
    string SMTConst(named_var out, string val);
    string SMTAdd(named_var in1, named_var in2, named_var out);
    string SMTConcat(named_var in1, named_var in2, named_var out);
    string SMTReg(named_var in, named_var clk, named_var out);    
    string SMTRegPE(named_var in, named_var clk, named_var out, named_var en);
    string SMTCounter(named_var clk, named_var en, named_var out);
    string SMTSlice(named_var in, named_var out, string low, string high);
  }
}
#endif
