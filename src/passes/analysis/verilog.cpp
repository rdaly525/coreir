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
            vAST::StringModule *module = new
                vAST::StringModule(verilog_json["verilog_string"].get<std::string>());
            modules.push_back(module);
            return;
        }
        return;
    }
    std::vector<vAST::Port *> ports;
    for (auto record : cast<RecordType>(module->getType())->getRecord()) {
        vAST::Identifier *name = new vAST::Identifier(record.first);
        Type* t = record.second;
        Type::DirKind direction = t->getDir();
        vAST::Direction verilog_direction;
        if (direction == Type::DK_In) {
            verilog_direction = vAST::INPUT;
        } else if (direction == Type::DK_Out) {
            verilog_direction = vAST::OUTPUT;
        } else if (direction == Type::DK_InOut) {
            verilog_direction = vAST::INOUT;
        } else {
            ASSERT(false, "Not implemented for direction = " + toString(direction));
        }
        ports.push_back(new vAST::Port(name, verilog_direction, vAST::WIRE));
    };
    std::vector<std::variant<vAST::StructuralStatement *, vAST::Declaration *>>
        body;
    for (auto instance : module->getDef()->getInstances()) {
        std::string module_name = instance.second->getModuleRef()->getLongName();
        vAST::Parameters instance_parameters;
        std::string instance_name = instance.first;
        std::map<std::string, std::variant<vAST::Identifier *, vAST::Index *, vAST::Slice *>>
            connections;
        for (auto connection : module->getDef()->getSortedConnections()) {
            if (connection.first->getSelectPath()[0] == "self" && connection.second->getSelectPath()[0] == instance_name) {
                connections.insert(
                        std::pair<std::string, vAST::Identifier *>(
                            connection.second->getSelectPath()[1],
                            new vAST::Identifier(connection.first->getSelectPath()[1])));
            } else if (connection.second->getSelectPath()[0] == "self" && connection.first->getSelectPath()[0] == instance_name) {
                connections.insert(
                        std::pair<std::string, vAST::Identifier *>(
                            connection.first->getSelectPath()[1],
                            new vAST::Identifier(connection.second->getSelectPath()[1])));

            } else {
                ASSERT(false, "NOT IMPLEMENTED");
            }
        }
        body.push_back(new vAST::ModuleInstantiation(module_name, instance_parameters, instance_name, connections));
    }
    vAST::Parameters parameters;
    vAST::Module *verilog_module = new vAST::Module(module->getLongName(), ports, body, parameters);
    modules.push_back(verilog_module);
}

bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  compileModule(node.getModule());
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
    for (auto module : modules) {
        os << module->toString() << std::endl;
    }
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
