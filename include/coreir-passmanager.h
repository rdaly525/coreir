#ifndef PASSMANAGER_HPP_
#define PASSMANAGER_HPP_

#include "coreir.h"
#include "coreir-passes.h"
#include "coreir-instancegraph.h"
#include <stack>

namespace CoreIR {

class InstanceGraph;
class PassManager {
  Context* c;
  vector<Namespace*> nss;

  //Data structure for storing passes
  std::unordered_map<string,Pass*> passMap;

  //Name to isValid
  std::unordered_map<string,bool> analysisPasses;

  vector<string> passLog;
  bool verbose = false;
  public:
    typedef vector<std::string> PassOrder;
    explicit PassManager(Context* c);
    ~PassManager();
    Context* getContext() { return c;}

    void addPass(Pass* p);

    //Runs all passes in order over namespaces
    //Returns if graph was modified
    bool run(PassOrder order, vector<string> namespaceName={"global"});

    void setVerbosity(bool v) { verbose = v;}
    void printLog();
    void printPassChoices();

    Pass* getAnalysisPass(std::string ID) {
      assert(passMap.count(ID));
      return passMap[ID];
    }

  private:
    void pushAllDependencies(string oname,stack<string> &work);

    friend class Pass;
    bool runPass(Pass* p);

    bool runNamespacePass(Pass* p);
    bool runModulePass(Pass* p);
    bool runInstancePass(Pass* p);
    bool runInstanceVisitorPass(Pass* p);
    bool runInstanceGraphPass(Pass* p);
};

}
#endif //PASSMANAGER_HPP_
