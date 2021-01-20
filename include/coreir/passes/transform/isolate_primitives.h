#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class IsolatePrimitives : public ModulePass {
 public:
  IsolatePrimitives()
      : ModulePass(
          "isolate_primitives",
          "Isolates all coreir/corebit primitives into its own module",
          false) {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes
}  // namespace CoreIR
