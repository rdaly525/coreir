#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include "coreir.h"
#include <ostream>
#include "vmodule.h"

namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  VerilogNamespace::VModules vmods;
  public :
    static std::string ID;
    Verilog() : InstanceGraphPass(ID,"Creates Verilog representation of IR",true) {}
    ~Verilog();
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      onlyTop = true;
      addDependency("verifyconnectivity --onlyinputs"); //Should change back to check all connections
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
