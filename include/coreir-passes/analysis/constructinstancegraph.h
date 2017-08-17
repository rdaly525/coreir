#ifndef CONSTRUCTINSTANCEGRAPH_HPP_
#define CONSTRUCTINSTANCEGRAPH_HPP_

#include "coreir.h"
#include "instancegraph.h"

namespace CoreIR {
namespace Passes {

class ConstructInstanceGraph : public NamespacePass {
  InstanceGraph* ig = nullptr;
  public :
    static std::string ID;
    ConstructInstanceGraph() : NamespacePass(ID,"Constructs the InstanceGraph",true) {
      ig = new InstanceGraph;
    }
    ~ConstructInstanceGraph() { delete ig;}
    bool runOnNamespace(Namespace* ns) override;
    void releaseMemory() override;
    InstanceGraph* getInstanceGraph() { return ig;}
};

}
}

#endif 
