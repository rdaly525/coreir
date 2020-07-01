#ifndef COREIR_PACKCONNECTIONS_HPP_
#define COREIR_PACKCONNECTIONS_HPP_

#include "coreir.h"

// Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

// This will add directed connection metadata to modules
class PackConnections : public ModulePass {

 public:
  PackConnections()
      : ModulePass(
          "packconnections",
          "Collapse bitwise connections into packed connections where "
          "possible") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
