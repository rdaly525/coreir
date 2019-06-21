#include <fstream>
#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/passes/analysis/verilog.h"
#include "coreir/tools/cxxopts.h"

namespace CoreIR {

// namespace {
// 
// void WriteModuleToStream(const Passes::VerilogNamespace::VModule* module,
//                          std::ostream& os) {
//   if (module->isExternal) {
//     // TODO(rsetaluri): Use "defer" like semantics to avoid duplicate calls to
//     // toString().
//     os << "/* External Modules" << std::endl;
//     os << module->toString() << std::endl;
//     os << "*/" << std::endl;
//     return;
//   }
//   os << module->toString() << std::endl;
// }
// 
// }  // namespace

void Passes::Verilog::initialize(int argc, char** argv) {
  cxxopts::Options options("verilog", "translates coreir graph to verilog");
  options.add_options()
    ("i,inline","Inline verilog modules if possible")
    ("y,verilator_debug","Mark IO and intermediate wires as /*verilator_public*/")
  ;
  auto opts = options.parse(argc,argv);
  if (opts.count("i")) {
    this->_inline = true;
  }
  if (opts.count("y")) {
    this->verilator_debug = true;
  }
}

std::string Passes::Verilog::ID = "verilog";

void Passes::Verilog::compileModule(Module* module) {
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getMetaData()["verilog"];
        if (verilog_json.count("verilog_string") > 0) {
            // Ensure that if the field verilog_string is included that the remaining
            // fields are not included.
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, field)                   \
              ASSERT(verilog_json.count(field) == 0,                                    \
                     string("Can not include ") +                               \
                     string(field) +                                            \
                     string(" with verilog_string"))
              VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "prefix");
              VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "definition");
              VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "interface");
              VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "parameters");
              VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "inlineable");
#undef VERILOG_FULL_MODULE_ASSERT_MUTEX
            // TODO(rsetaluri): Issue warning that we are including black-box
            // verilog. Most importantly the user should know that there is *no
            // guarantee* at this level that things are in sync. For example, if the
            // CoreIR module declaration does not match the verilog's, then the output
            // may be garbage for downstream tools.
            vAST::StringModule* module = new
                vAST::StringModule(verilog_json["verilog_string"].get<std::string>());
            std::vector<vAST::AbstractModule *> modules = {module};
            vAST::File *file = new vAST::File(modules);
            files.push_back(file);
            return;
        }
        return;
    }
}

bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  compileModule(node.getModule());
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
    ASSERT(false, "NOT IMPLEMENTED");
  // for (auto module : vmods.vmods) {
  //   if (vmods._inline && module->inlineable) {
  //     continue;
  //   }
  //   WriteModuleToStream(module, os);
  // }
}

void Passes::Verilog::writeToFiles(const std::string& dir) {
    ASSERT(false, "NOT IMPLEMENTED");
  // for (auto module : vmods.vmods) {
  //   if (vmods._inline && module->inlineable) {
  //     continue;
  //   }
  //   const std::string filename = dir + "/" + module->modname + ".v";
  //   std::ofstream fout(filename);
  //   ASSERT(fout.is_open(), "Cannot open file: " + filename);
  //   WriteModuleToStream(module, fout);
  //   fout.close();
  // }
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
