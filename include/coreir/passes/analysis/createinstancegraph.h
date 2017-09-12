#ifndef CREATEINSTANCEGRAPH_HPP_
#define CREATEINSTANCEGRAPH_HPP_

#include "coreir.h"
#include "coreir/ir/instancegraph.h"

namespace CoreIR {
namespace Passes {

class CreateInstanceGraph : public NamespacePass {
  InstanceGraph* ig = nullptr;
  public :
    static std::string ID;
    CreateInstanceGraph() : NamespacePass(ID,"Creates the InstanceGraph",true) {
      ig = new InstanceGraph;
    }
    ~CreateInstanceGraph() { delete ig;}
    bool runOnNamespace(Namespace* ns) override;
    void releaseMemory() override;
    InstanceGraph* getInstanceGraph() { return ig;}
};

}
}

#endif
