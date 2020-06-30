#pragma once

#include "coreir.h"

// Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

// This will add directed connection metadata to modules
class AddDummyInputs : public ModulePass {

 public:
  AddDummyInputs()
      : ModulePass(
          "add-dummy-inputs",
          "Connect any input ports that are unconnected to zero valued "
          "constants") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR
