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
  bool instanceGraphStale = true;

  std::map<uint,unordered_map<uint,vector<Pass*>>> passOrdering;
  public:
    explicit PassManager(Namespace* ns) : ns(ns) {}
    ~PassManager();
    //This will memory manage pass.
    void addPass(Pass* p, uint ordering);
    
    //Returns if graph was modified
    //Will also remove all the passes that were run
    bool run();
    void clear();
  private:
    bool runNamespacePass(vector<Pass*>& passes);
    bool runModulePass(vector<Pass*>& passes);
    bool runInstanceGraphPass(vector<Pass*>& passes);
};

}
#endif //PASSMANAGER_HPP_
