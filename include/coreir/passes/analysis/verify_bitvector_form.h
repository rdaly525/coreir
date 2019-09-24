#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will Verify that all modules have No unconnected ports
class VerifyBitvectorForm : public ModulePass {
  public :
    static std::string ID;
    VerifyBitvectorForm() : ModulePass(ID,"Verifies it is in BitVector form",true) {}
    void setAnalysisInfo() override {
      addDependency("verifyflattenedtypes");
      addDependency("verifyflatcoreirprims");
    }
    bool runOnModule(Module* m) override;

};

}
}
