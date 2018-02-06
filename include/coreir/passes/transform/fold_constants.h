#ifndef COREIR_FOLDCONSTANTS_HPP_
#define COREIR_FOLDCONSTANTS_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {

  bool foldConstants(CoreIR::Module* const mod);

namespace Passes {

  
//This will add directed connection metadata to modules
class FoldConstants : public ModulePass {
  
  public:
    static std::string ID;
    FoldConstants() : ModulePass(ID, "Evaluate constant expressions") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif

