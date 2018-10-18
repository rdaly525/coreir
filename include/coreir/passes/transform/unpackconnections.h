#ifndef COREIR_UNPACKCONNECTIONS_HPP_
#define COREIR_UNPACKCONNECTIONS_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {

  std::vector<Connection>
  unpackConnection(const CoreIR::Connection& conn);

  bool unpackConnections(CoreIR::Module* const mod);
  
namespace Passes {

//This will add directed connection metadata to modules
class UnpackConnections : public ModulePass {
  
  public:
    static std::string ID;
    UnpackConnections() : ModulePass(ID, "Collapse bitwise connections into unpacked connections where possible") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
