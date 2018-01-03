#ifndef COREIR_GROUPCONNECTIONS_HPP_
#define COREIR_GROUPCONNECTIONS_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class GroupConnections : public ModulePass {
  
  public:
    static std::string ID;
    GroupConnections() : ModulePass(ID, "Collapse bitwise connections into grouped connections where possible") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
