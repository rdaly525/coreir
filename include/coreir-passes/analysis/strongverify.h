#ifndef STRONGVERIFY_HPP_
#define STRONGVERIFY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will Verify that all modules have No unconnected ports
class StrongVerify : public ModulePass {
  public :
    static std::string ID;
    StrongVerify() : ModulePass(ID,"Strong Verification",true) {}
    void setAnalysisInfo() override {
      addDependency("verify");
    }
    bool runOnModule(Module* m) override;
};

}
}
#endif
