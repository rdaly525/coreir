#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class IsolatePrimitives : public ModulePass {
 public:
  static std::string ID;
  IsolatePrimitives()
      : ModulePass(
          ID,
          "Isolates all coreir/corebit primitives into its own module", false) {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes
}  // namespace CoreIR
