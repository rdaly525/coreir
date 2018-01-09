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
    CullZexts() : ModulePass(ID, "Collapse bitwise connections into packed connections where possible") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif

