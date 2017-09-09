#include "fuzzing.hpp"

#include "../src/simulator/sim.hpp"
#include "../src/simulator/print_c.hpp"

namespace CoreIR {

  std::string randomInputString(CoreIR::Type& tp, const std::string& var) {
    return var;
  }

  std::string ln(const std::string& s) {
    return s + ";\n";
  }

  std::string randomSimInputString(Module* mod) {
    auto args = simInputs(*mod);

    string res = "";
    for (auto& arg : args) {
      res += ln(randomInputString(*(arg.first), arg.second));
    }

    return res;
  }

}
