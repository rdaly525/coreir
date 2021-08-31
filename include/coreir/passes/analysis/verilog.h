#ifndef COREIR_VERILOG_HPP_
#define COREIR_VERILOG_HPP_

#include <memory>
#include <ostream>
#include "coreir.h"
#include "verilogAST.hpp"

namespace vAST = verilogAST;

namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  bool _inline = false;

  // Setting this to true will emit `/*verilator lint_off UNUSED */` around
  // certain primitives to avoid verilator lint errors
  bool verilator_compat = false;

  bool verilator_debug = false;
  bool disable_width_cast = false;

  std::string module_name_prefix = "";
  bool prefix_extern = false;

  // We store a vector of module name, module AST node pairs to support
  // serializing to a single or multiple files
  std::vector<std::pair<std::string, std::unique_ptr<vAST::AbstractModule>>>
    modules;
  std::map<Module*, std::string> linked_module_map;

  // Externally defined modules (no moduleDef), for now we just emit comments
  // listing them when compiling to a single file
  std::vector<Module*> extern_modules;

  // Set used to track generators that are compiled as parametrized verilog
  // modules. These parametrized modules have been instanced to create coreir
  // modules, but we only need to compile the verilog definition once
  std::set<Generator*> verilog_generators_seen;

  void compileModule(Module* module);

  std::vector<std::unique_ptr<vAST::AbstractPort>> compilePorts(
    RecordType* record_type);

  std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Vector>>
  processDecl(std::unique_ptr<vAST::Identifier> id, Type* type);

  void makeDecl(
    std::string name,
    Type* type,
    std::vector<std::variant<
      std::unique_ptr<vAST::StructuralStatement>,
      std::unique_ptr<vAST::Declaration>>>& declarations,
    bool is_reg);

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
  declareConnections(
    std::map<std::string, Instance*> instances,
    bool _inline,
    std::set<std::string>& instance_names,
    std::map<std::string, std::string>& non_input_port_map);

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
  compileModuleBody(
    RecordType* module_type,
    CoreIR::ModuleDef* definition,
    bool _inline,
    bool disable_width_cast,
    std::set<std::string>& wires,
    std::set<std::string>& inlined_wires);

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
  compileLinkedModuleBody(Module* module);

  std::unique_ptr<vAST::AbstractModule> compileStringBodyModule(
    json verilog_json,
    std::string name,
    Module* module);

  bool prefixAdded = false;
  void addPrefix();

 public:
  Verilog()
      : InstanceGraphPass("verilog", "Compiles IR to Verilog files", true) {}
  ~Verilog(){};
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
  void initialize(int argc, char** argv) override;
  void setAnalysisInfo() override {
    onlyTop = true;
    addDependency("verifyconnectivity --onlyinputs");  // Should change back to
                                                       // check all connections
    addDependency("verifyflattenedtypes --ndarray");
  }

  void clear() {
    using TModule = std::vector<
      std::pair<std::string, std::unique_ptr<vAST::AbstractModule>>>;
    TModule().swap(modules);
    extern_modules.clear();
    verilog_generators_seen.clear();
  }

  void writeToStream(std::ostream& os) override;
  void writeToFiles(
    const std::string& dir,
    std::unique_ptr<std::string> product_file,
    std::string outExt);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
