#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class ClockGate : public ModulePass {
 public:
  ClockGate()
      : ModulePass(
          "clock_gate",
          "Find all places where a clock enable register can be inserted and "
          "insert it") {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes
}  // namespace CoreIR
