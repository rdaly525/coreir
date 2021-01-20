#ifndef COREIR_TRANSFORM2COMBVIEW_HPP_
#define COREIR_TRANSFORM2COMBVIEW_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Transform2CombView : public InstanceGraphPass {
 public:
  Transform2CombView()
      : InstanceGraphPass(
          "transform2combview",
          "Transform2CombViews everything!") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;

  void setAnalysisInfo() override { addDependency("createcombview"); }
};

}  // namespace Passes
}  // namespace CoreIR
#endif
