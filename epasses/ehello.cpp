#include "coreir.h"
#include "coreir/passes/analysis/helloa.h"

using namespace CoreIR;

class EHello : public NamespacePass {
  public :
    static std::string ID;
    
    EHello() : NamespacePass(ID,"External Hello Transform") {}
    bool runOnNamespace(Namespace* n) override;
    void setAnalysisInfo() override {
      addDependency("helloa");
    }
};

string EHello::ID = "ehello";
bool EHello::runOnNamespace(Namespace* ns) {
  Passes::HelloA* dp = getAnalysisPass<Passes::HelloA>();
  cout << "EHello!" << endl;
  cout << "Dependent pass is: " << dp->getString() << endl;
  return false;
}

extern "C" Pass* registerPass() {
  return new EHello;
}

extern "C" void deletePass(Pass* p) {
  delete p;
}
