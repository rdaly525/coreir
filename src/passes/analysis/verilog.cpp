#include "coreir/passes/analysis/verilog.h"
#include <fstream>
#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
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
    while (type->getKind() == Type::TK_Named) {
        type = cast<NamedType>(type)->getRaw();
    }
    ASSERT(type->isBaseType(), "Expected Bit, or Array of Bits");
    return id;
}

void declare_connections(
    std::vector<Connection> connections,
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        &wire_declarations,
    std::map<Wireable *, std::string> &connection_map) {
    std::set<Wireable *> sources_seen;
    for (auto connection : connections) {
        if (connection.first->getSelectPath()[0] == "self" ||
            connection.second->getSelectPath()[0] == "self") {
            // These are wired up directly
            continue;
        }

        Type *type = connection.second->getType();
        Wireable *orig_source;
        Wireable *source;
        Wireable *sink;
        // If the second connection member is an output, we use it, otherwise
        // we use the first (even if it's an inout, this should be consistent)
        if (type->getDir() == Type::DK_Out) {
            orig_source = connection.second;
            sink = connection.first;
        } else {
            orig_source = connection.first;
            sink = connection.second;
        }
        // Types are flattened, so at most we have an array select
        ASSERT(orig_source->getSelectPath().size() <= 3,
               "Did not expect select path deeper than 3");
        if (orig_source->getSelectPath().size() == 3) {
            source = cast<Select>(orig_source)->getParent();
            type = source->getType();
        } else {
            source = orig_source;
        }
        std::string connection_name = orig_source->toString();
        std::replace(connection_name.begin(), connection_name.end(), '.', '_');
        connection_map[sink] = connection_name;
        if (sources_seen.count(source) == 0) {
            connection_name = source->toString();
            std::replace(connection_name.begin(), connection_name.end(), '.',
                         '_');
            std::unique_ptr<vAST::Identifier> id =
                std::make_unique<vAST::Identifier>(connection_name);
            // Can't find a simple way to "promote" a variant type to a
            // superset, so we just manually unpack it to call the Wire
            // constructor
            std::visit(
                [&](auto &&arg) -> void {
                    wire_declarations.push_back(
                        std::make_unique<vAST::Wire>(std::move(arg)));
                },
                process_decl(std::move(id), type));
        }
        connection_map[orig_source] = connection_name;
    }
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
            std::unique_ptr<vAST::AbstractModule> verilog_module =
                std::make_unique<vAST::StringModule>(
                    verilog_json["verilog_string"].get<std::string>());
            modules.push_back(std::move(verilog_module));
            return;
        }
        return;
    } else if (module->isGenerated() &&
               module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getGenerator()->getMetaData()["verilog"];
        std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
        for (auto port_str :
             verilog_json["interface"].get<std::vector<std::string>>()) {
            ports.push_back(std::make_unique<vAST::StringPort>(port_str));
        }
        vAST::Parameters parameters;
        std::set<std::string> parameters_seen;
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
        for (auto parameter : module->getModParams()) {
            if (parameters_seen.count(parameter.first) == 0) {
                // Old coreir backend defaults these (genparams without
                // defaults) to 0
                parameters.push_back(std::pair(
                    std::make_unique<vAST::Identifier>(parameter.first),
                    std::make_unique<vAST::NumericLiteral>("1")));
            }
        }
        std::unique_ptr<vAST::AbstractModule> string_body_module =
            std::make_unique<vAST::StringBodyModule>(
                make_name(module->getName(), verilog_json), std::move(ports),
                verilog_json["definition"].get<std::string>(),
                std::move(parameters));
        modules.push_back(std::move(string_body_module));
        verilog_generators_seen.insert(module->getGenerator());
        return;
    } else if (!module->hasDef()) {
        return;
    }
    std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
    for (auto record : cast<RecordType>(module->getType())->getRecord()) {
        std::unique_ptr<vAST::Identifier> name =
            std::make_unique<vAST::Identifier>(record.first);
        Type *type = record.second;
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
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        wire_declarations;
    std::map<Wireable *, std::string> connection_map;
    declare_connections(module->getDef()->getSortedConnections(),
                        wire_declarations, connection_map);

    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>>
        body;
    for (auto instance : module->getDef()->getInstances()) {
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
                                           std::unique_ptr<vAST::Slice>>>
            connections;
        for (auto connection : module->getDef()->getSortedConnections()) {
            if (connection.first->getSelectPath()[0] == "self" &&
                connection.second->getSelectPath()[0] == instance_name) {
                connections.insert(
                    std::pair<std::string, std::unique_ptr<vAST::Identifier>>(
                        connection.second->getSelectPath()[1],
                        std::make_unique<vAST::Identifier>(
                            connection.first->getSelectPath()[1])));
            } else if (connection.second->getSelectPath()[0] == "self" &&
                       connection.first->getSelectPath()[0] == instance_name) {
                connections.insert(
                    std::pair<std::string, std::unique_ptr<vAST::Identifier>>(
                        connection.first->getSelectPath()[1],
                        std::make_unique<vAST::Identifier>(
                            connection.second->getSelectPath()[1])));

            } else if (connection.first->getSelectPath()[0] == instance_name) {
                connections.insert(
                    std::pair<std::string, std::unique_ptr<vAST::Identifier>>(
                        connection.first->getSelectPath()[1],
                        std::make_unique<vAST::Identifier>(
                            connection_map[connection.first])));
            } else if (connection.second->getSelectPath()[0] == instance_name) {
                connections.insert(
                    std::pair<std::string, std::unique_ptr<vAST::Identifier>>(
                        connection.second->getSelectPath()[1],
                        std::make_unique<vAST::Identifier>(
                            connection_map[connection.second])));
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
    body.insert(body.begin(),
                std::make_move_iterator(wire_declarations.begin()),
                std::make_move_iterator(wire_declarations.end()));
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
    std::unique_ptr<vAST::AbstractModule> verilog_module =
        std::make_unique<vAST::Module>(module->getLongName(), std::move(ports),
                                       std::move(body), std::move(parameters));
    modules.push_back(std::move(verilog_module));
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
    for (auto &module : modules) {
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

}  // namespace CoreIR
