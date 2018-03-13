#pragma once

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class AddDummyInputs : public ModulePass {
  
  public:
    static std::string ID;
    AddDummyInputs() : ModulePass(ID, "Connect any input ports that are unconnected to zero valued constants") {}
    bool runOnModule(Module* m) override;
};

}
}
