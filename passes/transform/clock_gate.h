#pragma once

#include "ir/coreir.h"

namespace CoreIR {
namespace Passes {

class ClockGate : public ModulePass {
 public:
  static std::string ID;
  ClockGate()
      : ModulePass(
          ID,
          "Find all places where a clock enable register can be inserted and "
          "insert it") {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes
}  // namespace CoreIR
