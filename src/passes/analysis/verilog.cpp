#include "coreir/passes/analysis/verilog.h"
#include <fstream>
#include "coreir.h"
#include "coreir/tools/cxxopts.h"

namespace CoreIR {

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

std::string make_name(std::string name, json metadata) {
    if (metadata.count("prefix") > 0) {
        name = metadata["prefix"].get<std::string>() + name;
    }
    return name;
}

// Converts a CoreIR `Value` type into a Verilog literal
std::unique_ptr<vAST::Expression> convert_value(Value *value) {
    if (auto arg_value = dyn_cast<Arg>(value)) {
        return std::make_unique<vAST::Identifier>(arg_value->getField());
    } else if (auto int_value = dyn_cast<ConstInt>(value)) {
        return std::make_unique<vAST::NumericLiteral>(int_value->toString());
    } else if (auto bool_value = dyn_cast<ConstBool>(value)) {
        return std::make_unique<vAST::NumericLiteral>(
            std::to_string(uint(bool_value->get())));
    } else if (auto bit_vector_value = dyn_cast<ConstBitVector>(value)) {
        BitVector bit_vector = bit_vector_value->get();
        return std::make_unique<vAST::NumericLiteral>(
            bit_vector.hex_digits(), bit_vector.bitLength(), false, vAST::HEX);
    } else if (auto string_value = dyn_cast<ConstString>(value)) {
        return std::make_unique<vAST::String>(string_value->toString());
    }
    coreir_unreachable();
}

// Given a signal named `id` and a type `type`, wrap the signal name in a
// `Vector` node if the signal is of type Array
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Vector>>
process_decl(std::unique_ptr<vAST::Identifier> id, Type *type) {
    if (type->getKind() == Type::TK_Array) {
        ArrayType *array_type = cast<ArrayType>(type);
        ASSERT(array_type->getElemType()->isBaseType(),
               "Expected Array of Bits");
        return std::make_unique<vAST::Vector>(
            std::move(id),
            std::make_unique<vAST::NumericLiteral>(
                toString(array_type->getLen() - 1)),
            std::make_unique<vAST::NumericLiteral>("0"));
    }

    // unpack named types to get the raw type (so we can check that it's a
    // bit), iteratively because perhaps you can name and named type?
    // This is just a safety check for internal code, to improve performance,
    // we could guard this assert logic behind a macro
    while (type->getKind() == Type::TK_Named) {
        type = cast<NamedType>(type)->getRaw();
    }
    ASSERT(type->isBaseType(), "Expected Bit, or Array of Bits");

    // If it's not an Array type, just return the original identifier
    return std::move(id);
}

// Given a map of instances, return a vector of containing declarations for all
// the output ports of each instance.  We return a vector of a variant type for
// compatibility with the module AST node constructor, even though we only ever
// create Wire nodes.
std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                         std::unique_ptr<vAST::Declaration>>>
declare_connections(std::map<std::string, Instance *> instances) {
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        wire_declarations;
    for (auto instance : instances) {
        for (auto port :
             cast<RecordType>(instance.second->getModuleRef()->getType())
                 ->getRecord()) {
            if (port.second->getDir() == Type::DK_Out) {
                std::unique_ptr<vAST::Identifier> id =
                    std::make_unique<vAST::Identifier>(instance.first + "_" +
                                                       port.first);
                // Can't find a simple way to "promote" a variant type to a
                // superset, so we just manually unpack it to call the Wire
                // constructor
                std::visit(
                    [&](auto &&arg) -> void {
                        wire_declarations.push_back(
                            std::make_unique<vAST::Wire>(std::move(arg)));
                    },
                    process_decl(std::move(id), port.second));
            }
        }
    }
    return wire_declarations;
}

// Compiles a module defined with `verilog_string` in the `verilog` metadata
// field
std::unique_ptr<vAST::AbstractModule> compile_string_module(json verilog_json) {
    // Ensure that if the field verilog_string is included that the
    // remaining fields are not included.
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, field)     \
    ASSERT(verilog_json.count(field) == 0,                        \
           std::string("Can not include ") + std::string(field) + \
               std::string(" with verilog_string"))
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
    return std::make_unique<vAST::StringModule>(
        verilog_json["verilog_string"].get<std::string>());
}

// Compiles a module defined by the following entries in the `verilog` metadata
// field
// * "interface" -> used to define the module interface
// * "definition" -> used to define the module definition
//
// Parameters are defined by `getModParams`
// If the module `isGenerated`, the parameters to the module include
// `getDefaultGenArgs` and `getGenParams`
std::unique_ptr<vAST::AbstractModule> compile_string_body_module(
    json verilog_json, std::string name, Module *module) {
    std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
    for (auto port_str :
         verilog_json["interface"].get<std::vector<std::string>>()) {
        ports.push_back(std::make_unique<vAST::StringPort>(port_str));
    }
    vAST::Parameters parameters;
    std::set<std::string> parameters_seen;
    if (module->isGenerated()) {
        for (auto parameter : module->getGenerator()->getDefaultGenArgs()) {
            parameters.push_back(
                std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                          convert_value(parameter.second)));
            parameters_seen.insert(parameter.first);
        }
        for (auto parameter : module->getGenerator()->getGenParams()) {
            if (parameters_seen.count(parameter.first) == 0) {
                // Old coreir backend defaults these (genparams without
                // defaults) to 0
                parameters.push_back(std::pair(
                    std::make_unique<vAST::Identifier>(parameter.first),
                    std::make_unique<vAST::NumericLiteral>("1")));
            }
        }
    }
    for (auto parameter : module->getModParams()) {
        if (parameters_seen.count(parameter.first) == 0) {
            // Old coreir backend defaults these (genparams without
            // defaults) to 0
            parameters.push_back(
                std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                          std::make_unique<vAST::NumericLiteral>("1")));
        }
    }
    return std::make_unique<vAST::StringBodyModule>(
        name, std::move(ports), verilog_json["definition"].get<std::string>(),
        std::move(parameters));
}

// Compile a CoreIR record type corresponding to the interface of a module with
// flattened types into a vector of vAST Ports
std::vector<std::unique_ptr<vAST::AbstractPort>> compile_ports(
    RecordType *record_type) {
    std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
    for (auto entry : record_type->getRecord()) {
        std::unique_ptr<vAST::Identifier> name =
            std::make_unique<vAST::Identifier>(entry.first);

        Type *type = entry.second;
        Type::DirKind direction = type->getDir();

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

        ports.push_back(
            std::make_unique<vAST::Port>(process_decl(std::move(name), type),
                                         verilog_direction, vAST::WIRE));
    };
    return ports;
}

// Builds a map from pairs of strings of the form <instance_name, port_name>
// to the source Wireable which will be used to generate the verilog identifier
// corresponding to the wire connecting the two entities
//
// **TODO** Need to add support for inouts
std::map<std::pair<std::string, std::string>, std::vector<Wireable *>>
build_connection_map(std::vector<Connection> connections,
                     std::map<std::string, Instance *> instances) {
    std::map<std::pair<std::string, std::string>, std::vector<Wireable *>>
        connection_map;
    for (auto connection : connections) {
        for (auto instance : instances) {
            if (connection.first->getTopParent() == instance.second &&
                connection.first->getType()->getDir() == Type::DK_In) {
                connection_map[std::make_pair(
                                   instance.first,
                                   connection.first->getSelectPath()[1])]
                    .push_back(connection.second);
            } else if (connection.second->getTopParent() == instance.second &&
                       connection.second->getType()->getDir() == Type::DK_In) {
                connection_map[std::make_pair(
                                   instance.first,
                                   connection.second->getSelectPath()[1])]
                    .push_back(connection.first);
            }
        }
        if (connection.first->getSelectPath()[0] == "self" &&
            connection.first->getType()->getDir() == Type::DK_In) {
            connection_map[std::make_pair("self",
                                          connection.first->getSelectPath()[1])]
                .push_back(connection.second);
        } else if (connection.second->getSelectPath()[0] == "self" &&
                   connection.second->getType()->getDir() == Type::DK_In) {
            connection_map[std::make_pair(
                               "self", connection.second->getSelectPath()[1])]
                .push_back(connection.first);
        }
    }
    return connection_map;
}

void assign_module_outputs(
    RecordType *record_type,
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>> &body,
    std::map<std::pair<std::string, std::string>, std::vector<Wireable *>>
        connection_map) {
    for (auto port : record_type->getRecord()) {
        if (port.second->getDir() == Type::DK_In) {
            continue;
        }
        auto entry = connection_map[std::make_pair("self", port.first)];
        if (entry.size() == 0) {
            continue;
        } else if (entry.size() > 1) {
            std::vector<std::unique_ptr<vAST::Expression>> args;
            for (auto wireable : entry) {
                std::string connection_name = wireable->toString();
                connection_name = std::regex_replace(connection_name,
                                                     std::regex("self."), "");
                std::replace(connection_name.begin(), connection_name.end(),
                             '.', '_');
                args.push_back(
                    std::make_unique<vAST::Identifier>(connection_name));
            }
            std::unique_ptr<vAST::Concat> concat =
                std::make_unique<vAST::Concat>(std::move(args));
            body.push_back(std::make_unique<vAST::ContinuousAssign>(
                std::make_unique<vAST::Identifier>(port.first),
                std::move(concat)));
        } else {
            std::string connection_name = entry[0]->toString();
            connection_name =
                std::regex_replace(connection_name, std::regex("self."), "");
            std::replace(connection_name.begin(), connection_name.end(), '.',
                         '_');
            body.push_back(std::make_unique<vAST::ContinuousAssign>(
                std::make_unique<vAST::Identifier>(port.first),
                std::make_unique<vAST::Identifier>(connection_name)));
        }
    }
}

// Traverses the instance map and creates a vector of module instantiations
// using connection_map to wire up instance ports
// **TODO** More comments on this and how connection_map is used
std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                         std::unique_ptr<vAST::Declaration>>>
compile_module_body(RecordType *module_type,
                    std::vector<Connection> connections,
                    std::map<std::string, Instance *> instances) {
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        body = declare_connections(instances);

    std::map<std::pair<std::string, std::string>, std::vector<Wireable *>>
        connection_map = build_connection_map(connections, instances);

    for (auto instance : instances) {
        Module *instance_module = instance.second->getModuleRef();
        std::string module_name = instance_module->getName();
        if (instance_module->isGenerated()) {
            if (instance_module->getGenerator()->getMetaData().count(
                    "verilog") > 0) {
                json verilog_json =
                    instance_module->getGenerator()->getMetaData()["verilog"];
                module_name = make_name(module_name, verilog_json);
            } else {
                module_name = instance_module->getLongName();
            }
        }
        vAST::Parameters instance_parameters;
        std::string instance_name = instance.first;
        std::map<std::string, std::variant<std::unique_ptr<vAST::Identifier>,
                                           std::unique_ptr<vAST::Index>,
                                           std::unique_ptr<vAST::Slice>,
                                           std::unique_ptr<vAST::Concat>>>
            connections;
        for (auto port :
             cast<RecordType>(instance_module->getType())->getRecord()) {
            if (port.second->getDir() == Type::DK_Out) {
                connections.insert(std::make_pair(
                    port.first, std::make_unique<vAST::Identifier>(
                                    instance.first + "_" + port.first)));
                continue;
            }
            auto entry =
                connection_map[std::make_pair(instance.first, port.first)];
            if (entry.size() > 1) {
                std::vector<std::unique_ptr<vAST::Expression>> args;
                for (auto wireable : entry) {
                    std::string connection_name = wireable->toString();
                    connection_name = std::regex_replace(
                        connection_name, std::regex("self."), "");
                    std::replace(connection_name.begin(), connection_name.end(),
                                 '.', '_');
                    args.push_back(
                        std::make_unique<vAST::Identifier>(connection_name));
                }
                std::unique_ptr<vAST::Concat> concat =
                    std::make_unique<vAST::Concat>(std::move(args));
                connections.insert(
                    std::make_pair(port.first, std::move(concat)));
            } else {
                std::string connection_name = entry[0]->toString();
                connection_name = std::regex_replace(connection_name,
                                                     std::regex("self."), "");
                std::replace(connection_name.begin(), connection_name.end(),
                             '.', '_');
                connections.insert(std::make_pair(
                    port.first,
                    std::make_unique<vAST::Identifier>(connection_name)));
            }
        }
        if (instance.second->hasModArgs()) {
            for (auto parameter : instance.second->getModArgs()) {
                instance_parameters.push_back(std::pair(
                    std::make_unique<vAST::Identifier>(parameter.first),
                    convert_value(parameter.second)));
            }
        }
        if (instance_module->isGenerated() &&
            instance_module->getGenerator()->getMetaData().count("verilog") >
                0) {
            for (auto parameter :
                 instance.second->getModuleRef()->getGenArgs()) {
                instance_parameters.push_back(std::pair(
                    std::make_unique<vAST::Identifier>(parameter.first),
                    convert_value(parameter.second)));
            }
        }
        std::unique_ptr<vAST::StructuralStatement> statement =
            std::make_unique<vAST::ModuleInstantiation>(
                module_name, std::move(instance_parameters), instance_name,
                std::move(connections));
        body.push_back(std::move(statement));
    }
    assign_module_outputs(module_type, body, connection_map);
    return body;
}

void Passes::Verilog::compileModule(Module *module) {
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getMetaData()["verilog"];
        if (verilog_json.count("verilog_string") > 0) {
            // module is defined by a verilog string, we just emit the entire
            // string
            modules.push_back(std::make_pair(
                module->getName(), compile_string_module(verilog_json)));
            return;
        }
    } else if (module->isGenerated() &&
               module->getGenerator()->getMetaData().count("verilog") > 0) {
        // This module is an instance of generator defined as a parametrized
        // verilog module
        json verilog_json = module->getGenerator()->getMetaData()["verilog"];
        std::string name = make_name(module->getName(), verilog_json);

        modules.push_back(std::make_pair(
            name, compile_string_body_module(verilog_json, name, module)));

        // We only need to compile the verilog generator once, even though
        // there may be multiple instances of the generator represented as
        // different modules. We populate this set so that instance graph pass
        // can filter out other instnaces of the generator.
        verilog_generators_seen.insert(module->getGenerator());
        return;
    } else if (!module->hasDef()) {
        extern_modules.push_back(module);
        return;
    }
    std::vector<std::unique_ptr<vAST::AbstractPort>> ports =
        compile_ports(cast<RecordType>(module->getType()));

    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        body = compile_module_body(module->getType(),
                                   module->getDef()->getSortedConnections(),
                                   module->getDef()->getInstances());

    vAST::Parameters parameters;
    std::set<std::string> parameters_seen;
    if (module->getModParams().size()) {
        for (auto parameter : module->getDefaultModArgs()) {
            parameters.push_back(
                std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                          convert_value(parameter.second)));
            parameters_seen.insert(parameter.first);
        }
        for (auto parameter : module->getModParams()) {
            if (parameters_seen.count(parameter.first) == 0) {
                // Old coreir backend defaults these (genparams without
                // defaults) to 0
                parameters.push_back(std::pair(
                    std::make_unique<vAST::Identifier>(parameter.first),
                    std::make_unique<vAST::NumericLiteral>("1")));
            }
        }
    }
    std::string name = module->getLongName();
    std::unique_ptr<vAST::AbstractModule> verilog_module =
        std::make_unique<vAST::Module>(name, std::move(ports), std::move(body),
                                       std::move(parameters));
    modules.push_back(std::make_pair(name, std::move(verilog_module)));
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
    for (auto &module : extern_modules) {
        os << vAST::SingleLineComment("Module `" + module->getName() +
                                      "` defined externally")
                  .toString()
           << std::endl;
    }
    for (auto &module : modules) {
        os << module.second->toString() << std::endl;
    }
}

void Passes::Verilog::writeToFiles(const std::string &dir) {
    for (auto &module : modules) {
        const std::string filename = dir + "/" + module.first + ".v";
        std::ofstream output_file(filename);
        if (!output_file.is_open()) {
            throw std::runtime_error("Could not open file: " + filename);
        }
        output_file << module.second->toString() << std::endl;
        output_file.close();
    }
}

}  // namespace CoreIR
