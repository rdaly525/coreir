#ifndef COREIR_CLOCKIFYINTERFACE_HPP_
#define COREIR_CLOCKIFYINTERFACE_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
  class ClockifyInterface : public ModulePass {
  
  public:
    static std::string ID;
    ClockifyInterface() : ModulePass(ID, "Convert any BitIn fields in the interface that are only used as clocks into fields with named type coreir.clkIn") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
