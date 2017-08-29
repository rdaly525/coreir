#ifndef SMV_HPP_
#define SMV_HPP_

#include "coreir.h"
#include <ostream>
#include <string>
#include <set>
#include "smvmodule.hpp"
#include "smvoperators.hpp"

namespace CoreIR {
namespace Passes {

class SMV : public InstanceGraphPass {
  unordered_map<Instantiable*,SMVModule*> modMap;
  unordered_map<string, PropDef> properties;
  unordered_set<Instantiable*> external;
  // operators ignored by smv translation
  set<string> no_ops = {"term"};
  public :
    static std::string ID;
    SMV() : InstanceGraphPass(ID,"Creates SMV representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("strongverify");
      addDependency("verifyflattenedtypes");
      //      addDependency("verifyflatten");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
