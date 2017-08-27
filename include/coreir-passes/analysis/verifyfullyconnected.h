#ifndef STRONGVERIFY_HPP_
#define STRONGVERIFY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will Verify that all modules have No unconnected ports
class VerifyFullyConnected : public ModulePass {
  bool checkClkRst;
  public :
    static std::string ID;
    VerifyFullyConnected(bool checkClkRst = true) : ModulePass(ID + (checkClkRst ? "" : "-noclkrst"),"Strong Verification",true), checkClkRst(checkClkRst) {}
    void setAnalysisInfo() override {
      addDependency("verifyinputconnections");
    }
    bool runOnModule(Module* m) override;

  private:
    bool checkIfFullyConnected(Wireable* w, Error& e);
};

}
}
#endif
