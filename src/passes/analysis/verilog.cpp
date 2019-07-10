#include "coreir/passes/analysis/verilog.h"
#include <fstream>
#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/tools/cxxopts.h"

namespace CoreIR {

// namespace {
//
// void WriteModuleToStream(const Passes::VerilogNamespace::VModule* module,
//                          std::ostream& os) {
//   if (module->isExternal) {
//     // TODO(rsetaluri): Use "defer" like semantics to avoid duplicate calls
//     to
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

void Passes::Verilog::initialize(int argc, char **argv) {
    cxxopts::Options options("verilog", "translates coreir graph to verilog");
    options.add_options()("i,inline", "Inline verilog modules if possible")(
        "y,verilator_debug",
        "Mark IO and intermediate wires as /*verilator_public*/");
    auto opts = options.parse(argc, argv);
    if (opts.count("i")) {
        this->_inline = true;
    }
    if (opts.count("y")) {
        this->verilator_debug = true;
    }
}

std::string Passes::Verilog::ID = "verilog";

vAST::Expression *convert_value(Value *value) {
    if (auto arg_value = dyn_cast<Arg>(value)) {
        // return arg_value->getField();
        throw std::logic_error("NOT IMPLEMENTED: converting arg value" +
                               arg_value->getField());
    } else if (auto int_value = dyn_cast<ConstInt>(value)) {
        return new vAST::NumericLiteral(int_value->toString());
    } else if (auto bool_value = dyn_cast<ConstBool>(value)) {
        return new vAST::NumericLiteral(
            std::to_string(uint(bool_value->get())));
    } else if (auto bit_vector_value = dyn_cast<ConstBitVector>(value)) {
        BitVector bit_vector = bit_vector_value->get();
        return new vAST::NumericLiteral(
            bit_vector.hex_digits(), bit_vector.bitLength(), false, vAST::HEX);
    } else if (auto string_value = dyn_cast<ConstString>(value)) {
        return new vAST::String(string_value->toString());
    }
    coreir_unreachable();
}

std::string declare_connection(
    // TODO: It would be better if we just declared a wire for each
    // instance output, but this works for now by creating a unique wire
    // for all connections
    Connection connection, std::set<Connection> &declared_connections,
    std::vector<std::variant<vAST::StructuralStatement *, vAST::Declaration *>>
        &wire_declarations) {
    SelectPath first_select_path = connection.first->getSelectPath();
    SelectPath second_select_path = connection.second->getSelectPath();
    std::string name = first_select_path[0] + "_" + first_select_path[1] +
                       "__" + second_select_path[0] + "_" +
                       second_select_path[1];
    if (declared_connections.find(connection) == declared_connections.end()) {
        declared_connections.insert(connection);
        wire_declarations.push_back(new vAST::Wire(new vAST::Identifier(name)));
    }
    return name;
}

void Passes::Verilog::compileModule(Module *module) {
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getMetaData()["verilog"];
        if (verilog_json.count("verilog_string") > 0) {
            // Ensure that if the field verilog_string is included that the
            // remaining fields are not included.
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, field)           \
    ASSERT(verilog_json.count(field) == 0, string("Can not include ") + \
                                               string(field) +          \
                                               string(" with verilog_string"))
            VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "prefix");
            VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "definition");
            VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "interface");
            VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "parameters");
            VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, "inlineable");
#undef VERILOG_FULL_MODULE_ASSERT_MUTEX
            // TODO(rsetaluri): Issue warning that we are including black-box
            // verilog. Most importantly the user should know that there is *no
            // guarantee* at this level that things are in sync. For example, if
            // the CoreIR module declaration does not match the verilog's, then
            // the output may be garbage for downstream tools.
            vAST::StringModule *verilog_module = new vAST::StringModule(
                verilog_json["verilog_string"].get<std::string>());
            modules.push_back(verilog_module);
            return;
        }
        return;
    } else if (module->isGenerated() &&
               module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getGenerator()->getMetaData()["verilog"];
        std::vector<vAST::AbstractPort *> ports;
        for (auto port_str :
             verilog_json["interface"].get<std::vector<std::string>>()) {
            ports.push_back(new vAST::StringPort(port_str));
        }
        vAST::Parameters parameters;
        std::set<std::string> parameters_seen;
        for (auto parameter : module->getGenerator()->getDefaultGenArgs()) {
            parameters.push_back(
                std::pair(new vAST::Identifier(parameter.first),
                          convert_value(parameter.second)));
            parameters_seen.insert(parameter.first);
        }
        for (auto parameter : module->getGenerator()->getGenParams()) {
            if (parameters_seen.count(parameter.first) == 0) {
                // Old coreir backend defaults these (genparams without
                // defaults) to 0
                parameters.push_back(
                    std::pair(new vAST::Identifier(parameter.first),
                              new vAST::NumericLiteral("1")));
            }
        }
        vAST::StringBodyModule *string_body_module = new vAST::StringBodyModule(
            verilog_json["prefix"].get<std::string>() + module->getName(),
            ports, verilog_json["definition"].get<std::string>(),
            parameters);
        modules.push_back(string_body_module);
        verilog_generators_seen.insert(module->getGenerator());
        return;
    } else if (!module->hasDef()) {
        return;
    }
    std::vector<vAST::AbstractPort *> ports;
    for (auto record : cast<RecordType>(module->getType())->getRecord()) {
        vAST::Identifier *name = new vAST::Identifier(record.first);
        Type *t = record.second;
        Type::DirKind direction = t->getDir();
        vAST::Direction verilog_direction;
        if (direction == Type::DK_In) {
            verilog_direction = vAST::INPUT;
        } else if (direction == Type::DK_Out) {
            verilog_direction = vAST::OUTPUT;
        } else if (direction == Type::DK_InOut) {
            verilog_direction = vAST::INOUT;
        } else {
            ASSERT(false,
                   "Not implemented for direction = " + toString(direction));
        }
        ports.push_back(new vAST::Port(name, verilog_direction, vAST::WIRE));
    };
    std::set<Connection> declared_connections;
    std::vector<std::variant<vAST::StructuralStatement *, vAST::Declaration *>>
        wire_declarations;
    std::vector<std::variant<vAST::StructuralStatement *, vAST::Declaration *>>
        body;
    for (auto instance : module->getDef()->getInstances()) {
        Module *instance_module = instance.second->getModuleRef();
        std::string module_name = instance_module->getName();
        if (instance_module->isGenerated() &&
                instance_module->getGenerator()->getMetaData().count("verilog")
                > 0) {
            json verilog_json = instance_module->getGenerator()->getMetaData()["verilog"];
            module_name = verilog_json["prefix"].get<std::string>() + module_name;
        }
        vAST::Parameters instance_parameters;
        std::string instance_name = instance.first;
        std::map<std::string,
                 std::variant<vAST::Identifier *, vAST::Index *, vAST::Slice *>>
            connections;
        for (auto connection : module->getDef()->getSortedConnections()) {
            if (connection.first->getSelectPath()[0] == "self" &&
                connection.second->getSelectPath()[0] == instance_name) {
                connections.insert(std::pair<std::string, vAST::Identifier *>(
                    connection.second->getSelectPath()[1],
                    new vAST::Identifier(
                        connection.first->getSelectPath()[1])));
            } else if (connection.second->getSelectPath()[0] == "self" &&
                       connection.first->getSelectPath()[0] == instance_name) {
                connections.insert(std::pair<std::string, vAST::Identifier *>(
                    connection.first->getSelectPath()[1],
                    new vAST::Identifier(
                        connection.second->getSelectPath()[1])));

            } else if (connection.first->getSelectPath()[0] == instance_name) {
                std::string name = declare_connection(
                    connection, declared_connections, wire_declarations);
                connections.insert(std::pair<std::string, vAST::Identifier *>(
                    connection.first->getSelectPath()[1],
                    new vAST::Identifier(name)));
            } else if (connection.second->getSelectPath()[0] == instance_name) {
                std::string name = declare_connection(
                    connection, declared_connections, wire_declarations);
                connections.insert(std::pair<std::string, vAST::Identifier *>(
                    connection.second->getSelectPath()[1],
                    new vAST::Identifier(name)));
            }
        }
        if (instance.second->hasModArgs()) {
            for (auto parameter : instance.second->getModArgs()) {
                instance_parameters.push_back(
                    std::pair(new vAST::Identifier(parameter.first),
                              convert_value(parameter.second)));
            }
        }
        if (instance.second->getModuleRef()->isGenerated()) {
            for (auto parameter :
                 instance.second->getModuleRef()->getGenArgs()) {
                instance_parameters.push_back(
                    std::pair(new vAST::Identifier(parameter.first),
                              convert_value(parameter.second)));
            }
        }
        body.push_back(new vAST::ModuleInstantiation(
            module_name, instance_parameters, instance_name, connections));
    }
    body.insert(body.begin(), wire_declarations.begin(),
                wire_declarations.end());
    vAST::Parameters parameters;
    if (module->getModParams().size()) {
        throw std::logic_error(
            "NOT IMPLEMENTED: compiling parametrized module to verilog");
    }
    vAST::Module *verilog_module =
        new vAST::Module(module->getLongName(), ports, body, parameters);
    modules.push_back(verilog_module);
}

bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode &node) {
    Module *module = node.getModule();
    if (module->isGenerated() &&
            module->getGenerator()->getMetaData().count("verilog") > 0 &&
            verilog_generators_seen.count(module->getGenerator()) > 0) {
        return false;
    }
    compileModule(module);
    return false;
}

void Passes::Verilog::writeToStream(std::ostream &os) {
    for (auto module : modules) {
        os << module->toString() << std::endl;
    }
}

void Passes::Verilog::writeToFiles(const std::string &dir) {
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
    // set<VModule*> toDelete;
    // for (auto m : modMap) {
    //  toDelete.insert(m.second);
    //}
    // for (auto m : toDelete) {
    //  delete m;
    //}
}

}  // namespace CoreIR
