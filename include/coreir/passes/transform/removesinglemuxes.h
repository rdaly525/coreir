#ifndef REMOVESINGLEMUXES_HPP_
#define REMOVESINGLEMUXES_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveSingleMuxes : public ModulePass {
 public:
  RemoveSingleMuxes()
      : ModulePass(
          "removesinglemuxes",
          "Removes single-input muxes and their control signals, if they are "
          "not "
          "used elsewhere.") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
