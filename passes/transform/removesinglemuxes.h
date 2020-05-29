#ifndef REMOVESINGLEMUXES_HPP_
#define REMOVESINGLEMUXES_HPP_

#include "ir/coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveSingleMuxes : public ModulePass {
 public:
  static std::string ID;

  RemoveSingleMuxes()
      : ModulePass(
          ID,
          "Removes single-input muxes and their control signals, if they are "
          "not "
          "used elsewhere.") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
