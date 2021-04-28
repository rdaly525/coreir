#ifndef CREATEINSTANCEGRAPH_HPP_
#define CREATEINSTANCEGRAPH_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateInstanceGraph : public ContextPass {
  InstanceGraph* ig = nullptr;

 public:
  CreateInstanceGraph()
      : ContextPass("createinstancegraph", "Creates the InstanceGraph", true) {
    ig = new InstanceGraph;
  }
  ~CreateInstanceGraph() { delete ig; }
  bool runOnContext(Context* c) override;
  //void initialize(int argc, char** argv) override;
  void releaseMemory() override;
  InstanceGraph* getInstanceGraph() { return ig; }
};

}  // namespace Passes
}  // namespace CoreIR

#endif
