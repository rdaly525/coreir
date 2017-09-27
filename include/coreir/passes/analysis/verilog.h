#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include "coreir.h"
#include <ostream>
#include "vmodule.h"

namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  std::unordered_map<Instantiable*,VModule*> modMap;
  std::unordered_set<Instantiable*> external;
  public :
    static std::string ID;
    Verilog() : InstanceGraphPass(ID,"Creates Verilog representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity-onlyinputs"); //Should change back to check all connections
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
