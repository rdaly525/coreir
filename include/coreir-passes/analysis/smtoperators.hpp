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
  string SMTAnd(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
  string SMTOr(SmtBVVar in1, SmtBVVar in2, SmtBVVar out);
  string SMTNot(SmtBVVar in, SmtBVVar out);
  string SMTReg(SmtBVVar in, SmtBVVar clk, SmtBVVar out);

}
}
#endif
