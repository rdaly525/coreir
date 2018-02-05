#ifndef CREATEINSTANCEGRAPH_HPP_
#define CREATEINSTANCEGRAPH_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateInstanceGraph : public ContextPass {
  InstanceGraph* ig = nullptr;
  public :
    static std::string ID;
    CreateInstanceGraph() : ContextPass(ID,"Creates the InstanceGraph",true) {
      ig = new InstanceGraph;
    }
    ~CreateInstanceGraph() { delete ig;}
    bool runOnContext(Context* c) override;
    void releaseMemory() override;
    InstanceGraph* getInstanceGraph() { return ig;}
};

}
}

#endif
