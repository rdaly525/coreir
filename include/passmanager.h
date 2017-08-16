#ifndef PASSMANAGER_HPP_
#define PASSMANAGER_HPP_

#include "coreir.h"
#include "passes.h"
#include "instancegraph.h"

namespace CoreIR {

class InstanceGraph;
class PassManager {
  Context* c;
  
  //TODO Ad hoc, Find better system
  //Even better, construct this using a pass that is dependent
  //Need to add Analysys passes that can be used as dependencies
  //InstanceGraph* instanceGraph;
  //bool instanceGraphStale = true;

  //std::map<uint,unordered_map<uint,vector<Pass*>>> passOrdering;
  //Data structure for storing passes
  std::unordered_map<string,Pass*> passMap;

  //Name to isValid
  std::unordered_map<string,bool> analysisPasses;
  
  public:
    typedef vector<std::string> PassOrder;
    explicit PassManager(Context* c);
    ~PassManager();
    //This will memory manage pass.
    void addPass(Pass* p);
    
    //Returns if graph was modified
    //Will also remove all the passes that were run
    bool run(PassOrder order);
  private:
    friend class Pass;
    bool runPass(Pass* p);
    bool runNamespacePass(Pass* p);
    //bool runNamespacePass(vector<Pass*>& passes);
    //bool runModulePass(vector<Pass*>& passes);
    //bool runInstanceGraphPass(vector<Pass*>& passes);
};

}
#endif //PASSMANAGER_HPP_
