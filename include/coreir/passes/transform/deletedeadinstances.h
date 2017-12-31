#ifndef COREIR_DELETEDEADINSTANCES_HPP_
#define COREIR_DELETEDEADINSTANCES_HPP_

#include "coreir.h"

namespace CoreIR {

  bool deleteDeadInstances(CoreIR::Module* const mod);

  namespace Passes {

    class DeleteDeadInstances : public ModulePass {
    public:
      static std::string ID;
      DeleteDeadInstances() : ModulePass(ID, "Delete all instances with no outputs used") {}
      bool runOnModule(Module* m) override;
    };
  }

}

#endif
