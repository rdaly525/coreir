#ifndef PASSMANAGER_HPP_
#define PASSMANAGER_HPP_

#include "coreir.h"
#include "passes.h"
#include "instancegraph.h"

namespace CoreIR {

class PassManager {
  Namespace* ns;
  
  //TODO Ad hoc, Find better system
  //Even better, construct this using a pass that is dependent
  InstanceGraph instanceGraph;

  std::map<uint,unordered_map<uint,vector<Pass*>>> passOrdering;
  public:
    explicit PassManager(Namespace* ns) : ns(ns) {
      instanceGraph.construct(ns);
    }
    ~PassManager();
    //This will memory manage pass.
    void addPass(Pass* p, uint ordering);
    //Returns if graph was modified
    bool run();
  private:
    bool runModulePass(vector<Pass*>& passes);
    bool runInstanceGraphPass(vector<Pass*>& passes);
};

}
#endif //PASSMANAGER_HPP_
