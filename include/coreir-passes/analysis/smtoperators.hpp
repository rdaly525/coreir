#ifndef SMTOPERATORS_HPP_
#define SMTOPERATORS_HPP_

#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
  namespace Passes {

    string SMTgetNext(string var);
    string SMTAssign(Connection con);
    string SMTAnd(string in1, string in2, string out);
    string SMTOr(string in1, string in2, string out);
    string SMTNot(string in, string out);
    string SMTReg(string in, string clk, string out);
    string SMTConst(string out);

  }
}
#endif
