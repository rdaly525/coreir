#ifndef COREIR_REMOVECONSTDUPLICATES_HPP_
#define COREIR_REMOVECONSTDUPLICATES_HPP_

#include "coreir.h"

namespace CoreIR {

  namespace Passes {

    class RemoveConstDuplicates : public ModulePass {
    public:
      static std::string ID;
      RemoveConstDuplicates() : ModulePass(ID, "If a circuit contains more than one instance of a constant with the same value (e.g. 2 corebit.const instances that are both true) one of them is deleted and all outgoing connections from it are replaced") {}
      bool runOnModule(Module* m) override;
    };
  }

}

#endif
