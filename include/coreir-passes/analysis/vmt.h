#ifndef VMT_HPP_
#define VMT_HPP_

#include "coreir.h"
#include <ostream>
#include <string>
#include <set>
#include "vmtmodule.hpp"

using namespace CoreIR;
namespace CoreIR {
namespace Passes {

class VMT : public InstanceGraphPass {
  unordered_map<Instantiable*,VMTModule*> modMap;
  unordered_set<Instantiable*> external;
  // operators ignored by vmt translation
  set<string> no_ops = {"term"};
  public :
    static std::string ID;
    VMT() : InstanceGraphPass(ID,"Creates VMT representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("strongverify");
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
