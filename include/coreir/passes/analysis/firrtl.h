#ifndef COREIR_FIRRTL_HPP_
#define COREIR_FIRRTL_HPP_

#include "coreir.h"
#include <ostream>

namespace CoreIR {
namespace Passes {

using namespace std;
class FModule {
  Context* c;
  std::string name;
  std::vector<std::string> io;
  std::map<std::string,std::string> gparams;
  std::vector<std::string> params;
  std::vector<std::string> stmts;
  public : 
    FModule(Module* m) : c(m->getContext()), name(m->getLongName()) {
      addIO(cast<RecordType>(m->getType()));
      for (auto ppair : m->getModParams()) {
        auto vtype = ppair.second;
        uint n;
        if (isa<BoolType>(vtype)) n = 1;
        else if (auto bv = dyn_cast<BitVectorType>(vtype)) {
          n = bv->getWidth();
        }
        else ASSERT(0,"NYI");
        io.push_back("input " + ppair.first + " : UInt<" + std::to_string(n) + ">");
      }
      if (m->generated()) {
        checkJson(m->getGenerator()->getMetaData(),m->getGenArgs());
      }
    }
    std::string getName() { return name;}
    void checkJson(json jmeta,Values genargs) {
      if (jmeta.count("firrtl") ) {
        if (jmeta["firrtl"].count("prefix")) {
          this->name = jmeta["firrtl"]["prefix"].get<std::string>() + this->name;
        }
        if (jmeta["firrtl"].count("definition")) {
          for (auto stmt : jmeta["firrtl"]["definition"].get<std::vector<std::string>>()) {
            addStmt(stmt);
          }
        }
        if (jmeta["firrtl"].count("parameters")) {
          auto gp = (jmeta["firrtl"]["parameters"].get<std::vector<std::string>>());
          for (auto p : gp) {
            ASSERT(genargs.count(p),"Missing param" + p);
            if (p=="hi") { //Sketch annoying hack. Need to subtract 1 for indicies
              this->gparams["%"+p+"%"] = std::to_string(genargs[p]->get<int>()-1);
            }
            else {
              this->gparams["%"+p+"%"] = genargs[p]->toString();
            }
          }
        }
      }
    }
    bool hasDef() {return stmts.size()>0;}
    void addStmt(std::string stmt) {
      stmts.push_back(stmt);
    }
    void addIO(RecordType* rt) {
      for (auto rpair : rt->getRecord()) {
        Type* t = rpair.second;
        //Assumes mixed types are outputs
        addStmt(std::string(t->isInput() ? "input" : "output") + " " + rpair.first + " : " + type2firrtl(t,t->isInput()));
      }
    }
    //void addIO(vector<string> ios) {
    //  for (auto it : ios) io.push_back(it);
    //}
    std::string type2firrtl(Type* t, bool isInput);
    std::string toString();
};



class Firrtl : public InstanceGraphPass {
  std::map<Module*,FModule*> modMap;
  std::vector<FModule*> fmods;
  public :
    static std::string ID;
    Firrtl() : InstanceGraphPass(ID,"Creates Firrtl representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity-onlyinputs"); //Should change back to check all connections
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
