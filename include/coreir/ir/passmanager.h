#ifndef COREIR_PASSMANAGER_HPP_
#define COREIR_PASSMANAGER_HPP_

#include "fwd_declare.h"
#include <stack>

namespace CoreIR {

class InstanceGraph;
class PassManager {
  Context* c;
  std::vector<Namespace*> nss; 
  
  //Data structure for storing passes
  std::unordered_map<std::string,Pass*> passMap;

  //Name to isValid
  std::unordered_map<std::string,bool> analysisPasses;
  
  std::vector<std::string> passLog;
  bool verbose = false;
  public:
    typedef std::vector<std::string> PassOrder;
    explicit PassManager(Context* c);
    ~PassManager();
    Context* getContext() { return c;}
    
    void addPass(Pass* p);

    //Runs all passes in order over namespaces
    //Returns if graph was modified
    bool run(PassOrder order, std::vector<std::string> namespaceName={"global"});

    void setVerbosity(bool v) { verbose = v;}
    void printLog();
    void printPassChoices();

    Pass* getAnalysisPass(std::string ID) {
      assert(passMap.count(ID));
      return passMap[ID];
    }

  private:
    void pushAllDependencies(std::string oname,std::stack<std::string> &work);

    friend class Pass;
    bool runPass(Pass* p);

    bool runContextPass(Pass* p);
    bool runNamespacePass(Pass* p);
    bool runModulePass(Pass* p);
    bool runInstancePass(Pass* p);
    bool runInstanceVisitorPass(Pass* p);
    bool runInstanceGraphPass(Pass* p);
};

}
#endif //PASSMANAGER_HPP_
