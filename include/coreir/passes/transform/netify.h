#ifndef COREIR_NETIFY_HPP_
#define COREIR_NETIFY_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

  
//This will add directed connection metadata to modules
class Netify : public ModulePass {
  
  public:
    static std::string ID;
    Netify() : ModulePass(ID, "Transform circuit into netlist") {}
    void setAnalysisInfo() override {
      addDependency("verifyflattenedtypes");
      //addDependency("verifynobulkconnections");
    }
    bool runOnModule(Module* m) override;
};

}
}

#endif

