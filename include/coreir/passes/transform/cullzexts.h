#ifndef COREIR_CULLZEXTS_HPP_
#define COREIR_CULLZEXTS_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class CullZexts : public ModulePass {
  
  public:
    static std::string ID;
    CullZexts() : ModulePass(ID, "Remove zero extend nodes that extend from width N to width N") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif

