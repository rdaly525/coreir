#ifndef COREIR_DELETEDEADINSTANCES_HPP_
#define COREIR_DELETEDEADINSTANCES_HPP_

#include "coreir.h"

namespace CoreIR {

bool deleteDeadInstances(CoreIR::Module* const mod);

namespace Passes {

class DeleteDeadInstances : public ModulePass {
 public:
  DeleteDeadInstances()
      : ModulePass(
          "deletedeadinstances",
          "Delete all instances with no outputs used") {}
  bool runOnModule(Module* m) override;
};
}  // namespace Passes

}  // namespace CoreIR

#endif
