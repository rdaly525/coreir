#ifndef COREIR_MAGMA_HPP_
#define COREIR_MAGMA_HPP_

#include "coreir.h"
#include <ostream>

namespace CoreIR {
namespace Passes {

using namespace std;

class MModule {
  Context* c;
  Module* m;
  std::string name;
  std::vector<std::string> io;
  std::vector<std::string> stmts;
  public : 
    MModule(Module* m) : c(m->getContext()), m(m) {
      this->name = this->toName(m);
      this->addIO(cast<RecordType>(m->getType()));
    }
    std::string toName(Module* m);
    std::string getName() { return name;}
    bool hasDef() {return stmts.size()>0;}
    void addStmt(std::string stmt) {
      stmts.push_back(stmt);
    }
    void addIO(RecordType* rt);
    std::string toInstanceString(string iname,Values modargs);
    std::string toString();
};

class Magma : public InstanceGraphPass {
  std::map<Generator*,MModule*> genMap;
  std::map<Module*,MModule*> modMap;
  std::vector<MModule*> mmods;
  public :
    static std::string ID;
    Magma() : InstanceGraphPass(ID,"Creates Magma representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity-onlyinputs");
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
