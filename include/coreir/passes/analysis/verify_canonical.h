#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

// Canonical Form:
// TODO(rdaly): Add a good description.

class VerifyCanonical : public ModulePass {
 public:
  static std::string ID;
  VerifyCanonical()
      : ModulePass(ID, "Verifies it is in BitVector form", true) {}

  bool runOnModule(Module* m) override;
};

}  // namespace CoreIR
}  // namespace Passes
