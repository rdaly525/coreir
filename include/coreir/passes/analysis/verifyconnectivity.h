#ifndef COREIR_VERIFY_CONNECTIVITY_HPP_
#define COREIR_VERIFY_CONNECTIVITY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will Verify that all modules have No unconnected ports
class VerifyConnectivity : public ModulePass {
  bool onlyInputs = false;
  bool checkClkRst = true;
  public :
    static std::string ID;
    VerifyConnectivity(bool onlyInputs=false, bool checkClkRst = true) : ModulePass(ID + (onlyInputs ? "-onlyinputs" : "") + (checkClkRst ? "" : "-noclkrst"),"Checks connectivity",true), onlyInputs(onlyInputs), checkClkRst(checkClkRst) {}
    void setAnalysisInfo() override {
      addDependency("verifyinputconnections");
    }
    bool runOnModule(Module* m) override;
    bool finalize() override {
      getContext()->checkerrors();
      return false;
    }

  private:
    bool checkIfFullyConnected(Wireable* w, Error& e);
};

}
}
#endif
