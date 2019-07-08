#include <fstream>
#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/passes/analysis/verilog.h"
#include "coreir/tools/cxxopts.h"

namespace CoreIR {

namespace {

void WriteModuleToStream(const Passes::VerilogNamespace::VModule* module,
                         std::ostream& os) {
  if (module->isExternal) {
    // TODO(rsetaluri): Use "defer" like semantics to avoid duplicate calls to
    // toString().
    os << "/* External Modules" << std::endl;
    os << module->toString() << std::endl;
    os << "*/" << std::endl;
    return;
  }
  os << module->toString() << std::endl;
}

}  // namespace

void Passes::Verilog::initialize(int argc, char** argv) {
  cxxopts::Options options("verilog", "translates coreir graph to verilog and optionally inlines primitives");
  options.add_options()
    ("i,inline","Inline verilog modules if possible")
    ("y,verilator_debug","Mark IO and intermediate wires as /*verilator_public*/")
  ;
  auto opts = options.parse(argc,argv);
  if (opts.count("i")) {
    this->vmods._inline = true;
  }
  if (opts.count("y")) {
    this->vmods._verilator_debug = true;
  }
}

std::string Passes::Verilog::ID = "verilog";
bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  
  //Create a new Vmodule for this node
  Module* m = node.getModule();
  
  vmods.addModule(m);
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  for (auto module : vmods.vmods) {
    if (vmods._inline && module->inlineable) {
      continue;
    }
    WriteModuleToStream(module, os);
  }
}

void Passes::Verilog::writeToFiles(const std::string& dir,
                                   std::unique_ptr<std::string> product_file) {
  std::vector<std::string> products;
  for (auto module : vmods.vmods) {
    if (vmods._inline && module->inlineable) continue;
    const std::string filename = module->modname + ".v";
    products.push_back(filename);
    const std::string full_filename = dir + "/" + filename;
    std::ofstream fout(full_filename);
    ASSERT(fout.is_open(), "Cannot open file: " + full_filename);
    WriteModuleToStream(module, fout);
    fout.close();
  }
  // Write out the product list, if requested.
  if (!product_file) return;
  std::ofstream fout(*product_file);
  ASSERT(fout.is_open(), "Cannot open file: " + *product_file);
  for (const auto& product : products) {
    fout << product << "\n";
  }
  fout.close();
}

Passes::Verilog::~Verilog() {
  //set<VModule*> toDelete;
  //for (auto m : modMap) {
  //  toDelete.insert(m.second);
  //}
  //for (auto m : toDelete) {
  //  delete m;
  //}
}

}
