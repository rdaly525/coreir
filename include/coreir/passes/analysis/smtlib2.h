#ifndef SMTLIB2_HPP_
#define SMTLIB2_HPP_

#include "coreir.h"
#include <ostream>
#include <string>
#include <set>
#include "smtmodule.hpp"

using namespace CoreIR;
namespace CoreIR {
namespace Passes {

class SmtLib2 : public InstanceGraphPass {
  unordered_map<Module*,SMTModule*> modMap;
  unordered_set<Module*> external;
  // operators ignored by smt translation
  set<string> no_ops = {"term"};
  public :
    static std::string ID;
    SmtLib2() : InstanceGraphPass(ID,"Creates SmtLib2 representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity-onlyinputs-noclkrst");
      addDependency("verifyflattenedtypes");
      addDependency("verifyflatcoreirprims");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
