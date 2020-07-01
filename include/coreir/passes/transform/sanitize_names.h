#ifndef COREIR_SANITIZENAMES_HPP_
#define COREIR_SANITIZENAMES_HPP_

#include "coreir.h"

// Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

// This will add directed connection metadata to modules
class SanitizeNames : public ModulePass {

 public:
  SanitizeNames()
      : ModulePass(
          "sanitize-names",
          "Change names to only include verilog and C++ legal identifiers") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
