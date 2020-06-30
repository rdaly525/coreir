#ifndef COREIR_VERIFY_CONNECTIVITY_HPP_
#define COREIR_VERIFY_CONNECTIVITY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

// This will Verify that all modules have No unconnected ports
class VerifyConnectivity : public ModulePass {
  bool onlyInputs = false;
  bool checkClkRst = true;

 public:
  VerifyConnectivity() : ModulePass("verifyconnectivity", "Checks connectivity", true) {}
  void setAnalysisInfo() override { addDependency("verifyinputconnections"); }
  void initialize(int argc, char** argv) override;
  bool runOnModule(Module* m) override;
  bool finalize() override {
    getContext()->checkerrors();
    return false;
  }

 private:
  bool checkIfFullyConnected(Wireable* w, Error& e);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
