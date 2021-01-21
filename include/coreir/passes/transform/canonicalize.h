#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Canonicalize: public ModulePass {
 public:
  Canonicalize()
      : ModulePass(
          "canonicalize",
          "puts all modules into canonical form (described in TODO)") {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes
}  // namespace CoreIR
