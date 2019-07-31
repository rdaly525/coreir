#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include "coreir.h"
#include "verilogAST.hpp"
#include <memory>
#include <ostream>

namespace vAST = verilogAST;

namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  bool _inline = false;
  bool verilator_debug = false;

  // We store a vector of module name, module AST node pairs to support
  // serializing to a single or multiple files
  std::vector<std::pair<std::string, std::unique_ptr<vAST::AbstractModule>>>
      modules;

  // Externally defined modules (no moduleDef), for now we just emit comments
  // listing them when compiling to a single file
  std::vector<Module *> extern_modules;

  // Set used to track generators that are compiled as parametrized verilog
  // modules. These parametrized modules have been instanced to create coreir
  // modules, but we only need to compile the verilog definition once
  std::set<Generator *> verilog_generators_seen;

  void compileModule(Module *module);

    std::vector<std::unique_ptr<vAST::AbstractPort>>
    compilePorts(RecordType *record_type);

  std::unique_ptr<vAST::AbstractModule>
  compileStringBodyModule(json verilog_json, std::string name, Module *module);

public:
  static std::string ID;
  Verilog() : InstanceGraphPass(ID, "Compiles IR to Verilog files", true) {}
  ~Verilog(){};
  bool runOnInstanceGraphNode(InstanceGraphNode &node) override;
  void initialize(int argc, char **argv) override;
  void setAnalysisInfo() override {
    onlyTop = true;
    addDependency("verifyconnectivity --onlyinputs"); // Should change back to
                                                      // check all connections
    addDependency("verifyflattenedtypes");
  }

  void writeToStream(std::ostream &os);
  void writeToFiles(const std::string &dir,
                    std::unique_ptr<std::string> product_file);
};

} // namespace Passes
} // namespace CoreIR
#endif
