#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include <memory>
#include <ostream>
#include "coreir.h"
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
    void initialize(int argc, char** argv) override;
    void setAnalysisInfo() override {
      onlyTop = true;
      addDependency("verifyconnectivity --onlyinputs"); //Should change back to check all connections
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
    void writeToFiles(const std::string& dir,
                      std::unique_ptr<string> product_file);
};

}
}
#endif
