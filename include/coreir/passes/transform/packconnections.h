#ifndef COREIR_PACKCONNECTIONS_HPP_
#define COREIR_PACKCONNECTIONS_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class PackConnections : public ModulePass {
  
  public:
    static std::string ID;
    PackConnections() : ModulePass(ID, "Collapse bitwise connections into packed connections where possible") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
