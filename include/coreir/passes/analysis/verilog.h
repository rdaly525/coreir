#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include "coreir.h"
#include <ostream>
#include "vmodule.h"
#include "verilogAST.hpp"

namespace vAST = verilogAST;

namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  bool _inline = false;
  bool verilator_debug = true;

  std::vector<vAST::File*> files;

  void compileModule(Module* module);
  public :
    static std::string ID;
    Verilog() : InstanceGraphPass(ID,"Compiles IR to Verilog files",true) {}
    ~Verilog();
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void initialize(int argc, char** argv) override;
    void setAnalysisInfo() override {
      onlyTop = true;
      addDependency("verifyconnectivity --onlyinputs"); //Should change back to check all connections
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
    void writeToFiles(const std::string& dir);
};

}
}
#endif
