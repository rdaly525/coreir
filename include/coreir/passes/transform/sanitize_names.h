#ifndef COREIR_SANITIZENAMES_HPP_
#define COREIR_SANITIZENAMES_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class SanitizeNames : public ModulePass {
  
  public:
    static std::string ID;
    SanitizeNames() : ModulePass(ID, "Change names to only include verilog and C++ legal identifiers") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif

