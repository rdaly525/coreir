#include "fuzzing.hpp"

#include "../src/simulator/sim.hpp"
#include "../src/simulator/print_c.hpp"

namespace CoreIR {

  std::string ln(const std::string& s) {
    return s + ";\n";
  }

  std::string primitiveRandomInputString(CoreIR::Type& t, const std::string& var) {
    assert(isPrimitiveType(t));

    return ln(cPrimitiveTypeString(t) + " " + var + " = rand()");
  }

  std::string randomInputString(CoreIR::Type& tp, const std::string& var) {
    if (isPrimitiveType(tp)) {
      return primitiveRandomInputString(tp, var);
    }

    return "var!!;";
      //assert(false);
  }

  std::string randomSimInputString(Module* mod) {
    auto args = simInputs(*mod);

    string res = "";
    for (auto& arg : args) {
      res += randomInputString(*(arg.first), arg.second);
    }

    return res;
  }

}
