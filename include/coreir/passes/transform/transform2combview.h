#ifndef COREIR_TRANSFORM2COMBVIEW_HPP_
#define COREIR_TRANSFORM2COMBVIEW_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Transform2CombView : public InstanceGraphPass {
  public :
    static std::string ID;
    Transform2CombView() : InstanceGraphPass(ID,"Transform2CombViews everything!") {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;

    void setAnalysisInfo() override {
      addDependency("createcombview");
    }

};

}
}
#endif
