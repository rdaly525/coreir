#include "coreir/common/logging_lite.hpp"
#include "coreir/passes/analysis/verilog.h"
#include "coreir.h"
#include "coreir/tools/cxxopts.h"
#include "verilogAST/transformer.hpp"
#include "verilogAST/assign_inliner.hpp"
#include <fstream>

namespace vAST = verilogAST;

class UnaryOpReplacer : public vAST::Transformer {
    std::unique_ptr<vAST::Expression> in;
  public:
  UnaryOpReplacer(std::unique_ptr<vAST::Expression> in) :
        in(std::move(in)){};

  virtual std::unique_ptr<vAST::Expression> visit(
      std::unique_ptr<vAST::Expression> node) {
    if (auto ptr = dynamic_cast<vAST::Identifier *>(node.get())) {
      node.release();
      std::unique_ptr<vAST::Identifier> id(ptr);
      if (id->value == "in") {
        return std::move(this->in);
      }
      return vAST::Transformer::visit(std::move(id));
    }
    return vAST::Transformer::visit(std::move(node));
  };
};

class BinaryOpReplacer : public vAST::Transformer {
    std::unique_ptr<vAST::Expression> in0;
    std::unique_ptr<vAST::Expression> in1;
  public:
  BinaryOpReplacer(std::unique_ptr<vAST::Expression> in0,
                   std::unique_ptr<vAST::Expression> in1) :
        in0(std::move(in0)), in1(std::move(in1)){};

  virtual std::unique_ptr<vAST::Expression> visit(
      std::unique_ptr<vAST::Expression> node) {
    if (auto ptr = dynamic_cast<vAST::Identifier *>(node.get())) {
      node.release();
      std::unique_ptr<vAST::Identifier> id(ptr);
      if (id->value == "in0") {
        return std::move(this->in0);
      } else if (id->value == "in1") {
        return std::move(this->in1);
      }
      return vAST::Transformer::visit(std::move(id));
    }
    return vAST::Transformer::visit(std::move(node));
  };
};

class MuxReplacer : public vAST::Transformer {
    std::unique_ptr<vAST::Expression> in0;
    std::unique_ptr<vAST::Expression> in1;
    std::unique_ptr<vAST::Expression> sel;
  public:
  MuxReplacer(std::unique_ptr<vAST::Expression> in0,
              std::unique_ptr<vAST::Expression> in1,
              std::unique_ptr<vAST::Expression> sel) :
        in0(std::move(in0)), in1(std::move(in1)), sel(std::move(sel)){};

  virtual std::unique_ptr<vAST::Expression> visit(
      std::unique_ptr<vAST::Expression> node) {
    if (auto ptr = dynamic_cast<vAST::Identifier *>(node.get())) {
      node.release();
      std::unique_ptr<vAST::Identifier> id(ptr);
      if (id->value == "in0") {
        return std::move(this->in0);
      } else if (id->value == "in1") {
        return std::move(this->in1);
      } else if (id->value == "sel") {
        return std::move(this->sel);
      }
      return vAST::Transformer::visit(std::move(id));
    }
    return vAST::Transformer::visit(std::move(node));
  };
};

bool is_inlined(std::string primitive_type, std::string name) {
    return primitive_type == "binary" || primitive_type == "unary" ||
        primitive_type == "unaryReduce" || primitive_type == "binaryReduce" ||
        (primitive_type == "other" && 
         (name == "const" || name == "mux" || name == "slice"));
}

bool can_inline_binary_op(CoreIR::Module *module, bool _inline) {
    if (module->isGenerated() &&
        module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getGenerator()->getMetaData()["verilog"];
        return module->getGenerator()->hasPrimitiveExpressionLambda() &&
            (verilog_json["primitive_type"] == "binary" ||
             verilog_json["primitive_type"] == "binaryReduce")
            && _inline;
    }
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getMetaData()["verilog"];
        return module->hasPrimitiveExpressionLambda() &&
            (verilog_json["primitive_type"] == "binary" ||
             verilog_json["primitive_type"] == "binaryReduce")
            && _inline;
    }
    return false;
}

std::unique_ptr<vAST::Expression> get_primitive_expr(CoreIR::Instance *instance) {
    CoreIR::Module *module = instance->getModuleRef();
    if (module->isGenerated()) {
        return module->getGenerator()->getPrimitiveExpressionLambda()();
    }
    return module->getPrimitiveExpressionLambda()();
}

std::unique_ptr<vAST::StructuralStatement> inline_binary_op(
    std::pair<std::string, CoreIR::Instance *> instance,
    std::unique_ptr<vAST::Connections> verilog_connections) {
  BinaryOpReplacer transformer(verilog_connections->at("in0"),
                               verilog_connections->at("in1"));
  return std::make_unique<vAST::ContinuousAssign>(
      std::make_unique<vAST::Identifier>(instance.first + "_out"),
      transformer.visit(get_primitive_expr(instance.second)));
}

bool can_inline_unary_op(CoreIR::Module *module, bool _inline) {
    if (module->isGenerated() &&
        module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getGenerator()->getMetaData()["verilog"];
        return module->getGenerator()->hasPrimitiveExpressionLambda() &&
            (verilog_json["primitive_type"] == "unary" ||
             verilog_json["primitive_type"] == "unaryReduce")
            && _inline;
    }
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getMetaData()["verilog"];
        return module->hasPrimitiveExpressionLambda() &&
            (verilog_json["primitive_type"] == "unary" ||
             verilog_json["primitive_type"] == "unaryReduce")
            && _inline;
    }
    return false;
}

std::unique_ptr<vAST::StructuralStatement> inline_unary_op(
    std::pair<std::string, CoreIR::Instance *> instance,
    std::unique_ptr<vAST::Connections> verilog_connections) {
  UnaryOpReplacer transformer(verilog_connections->at("in"));
  return std::make_unique<vAST::ContinuousAssign>(
      std::make_unique<vAST::Identifier>(instance.first + "_out"),
      transformer.visit(get_primitive_expr(instance.second)));
}

bool can_inline_const_op(CoreIR::Module *module, bool _inline) {
    if (module->isGenerated() &&
        module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getGenerator()->getMetaData()["verilog"];
        return module->getGenerator()->hasPrimitiveExpressionLambda() &&
            verilog_json["primitive_type"] == "other" &&
            module->getName() == "const" && _inline;
    }
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json = module->getMetaData()["verilog"];
        return module->hasPrimitiveExpressionLambda() &&
            verilog_json["primitive_type"] == "other" &&
            module->getName() == "const" && _inline;
    }
    return false;
}

bool can_inline_mux_op(CoreIR::Module *module, bool _inline) {
    if (module->isGenerated() &&
        module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getGenerator()->getMetaData()["verilog"];
        return module->getGenerator()->hasPrimitiveExpressionLambda() &&
            verilog_json["primitive_type"] == "other" &&
            module->getName() == "mux" && _inline;
    }
    if (module->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getMetaData()["verilog"];
        return module->hasPrimitiveExpressionLambda() &&
            verilog_json["primitive_type"] == "other" &&
            module->getName() == "mux" && _inline;
    }
    return false;
}

std::unique_ptr<vAST::StructuralStatement> inline_mux_op(
    std::pair<std::string, CoreIR::Instance *> instance,
    std::unique_ptr<vAST::Connections> verilog_connections) {
  MuxReplacer transformer(verilog_connections->at("in0"),
                          verilog_connections->at("in1"),
                          verilog_connections->at("sel"));
  return std::make_unique<vAST::ContinuousAssign>(
      std::make_unique<vAST::Identifier>(instance.first + "_out"),
      transformer.visit(get_primitive_expr(instance.second)));
}

bool can_inline_slice_op(CoreIR::Module *module, bool _inline) {
    if (module->isGenerated() &&
        module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            module->getGenerator()->getMetaData()["verilog"];
        return module->getGenerator()->hasPrimitiveExpressionLambda() &&
            verilog_json["primitive_type"] == "other" &&
            module->getName() == "slice" && _inline;
    }
    return false;
}

// Unpack variant type and convert to parent type Expression
std::unique_ptr<vAST::Expression>
convert_to_expression(std::variant<std::unique_ptr<vAST::Identifier>,
                                   std::unique_ptr<vAST::Index>> value) {
  return std::visit([](auto &&value) -> std::unique_ptr<vAST::Expression> {
    return std::move(value); 
  }, value);
}

// Unpack variant type and convert to assign variant type
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Index>,
             std::unique_ptr<vAST::Slice>> 
convert_to_assign_target(std::variant<std::unique_ptr<vAST::Identifier>,
                         std::unique_ptr<vAST::Index>> value) {
  return std::visit([](auto &&value) ->
    std::variant<std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::Index>, std::unique_ptr<vAST::Slice>> 
    { return std::move(value); }, 
    value
  );
}

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

// Helper function that prepends a prefix contained in json metadata if it
// exists
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
        std::to_string(uint(bool_value->get())), 1, false, vAST::BINARY);
  } else if (auto bit_vector_value = dyn_cast<ConstBitVector>(value)) {
    BitVector bit_vector = bit_vector_value->get();
    return std::make_unique<vAST::NumericLiteral>(
        bit_vector.hex_digits(), bit_vector.bitLength(), false, vAST::HEX);
  } else if (auto string_value = dyn_cast<ConstString>(value)) {
    return std::make_unique<vAST::String>(string_value->toString());
  }
  coreir_unreachable();
}

// unpack named types to get the raw type (so we can check that it's a
// bit), iteratively because perhaps you can name and named type?
// This is just a safety check for internal code, to improve performance,
// we could guard this assert logic behind a macro
Type *get_raw_type(Type *type) {
  while (isa<NamedType>(type)) {
    type = cast<NamedType>(type)->getRaw();
  }
  return type;
}

// Given a signal named `id` and a type `type`, wrap the signal name in a
// `Vector` node if the signal is of type Array
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Vector>>
process_decl(std::unique_ptr<vAST::Identifier> id, Type *type) {
  if (isa<ArrayType>(type)) {
    ArrayType *array_type = cast<ArrayType>(type);
    Type *internal_type = get_raw_type(array_type->getElemType());
    ASSERT(internal_type->isBaseType(), "Expected Array of Bits");
    return std::make_unique<vAST::Vector>(
        std::move(id),
        std::make_unique<vAST::NumericLiteral>(
            toString(array_type->getLen() - 1)),
        std::make_unique<vAST::NumericLiteral>("0"));
  }

  type = get_raw_type(type);
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
    RecordType *record_type =
        cast<RecordType>(instance.second->getModuleRef()->getType());
    for (auto field : record_type->getFields()) {
      Type *field_type = record_type->getRecord().at(field);
      if (!field_type->isInput()) {
        std::unique_ptr<vAST::Identifier> id =
            std::make_unique<vAST::Identifier>(instance.first + "_" + field);
        // Can't find a simple way to "convert" a variant type to a
        // superset, so we just manually unpack it to call the Wire
        // constructor
        std::visit(
            [&](auto &&arg) -> void {
              wire_declarations.push_back(
                  std::make_unique<vAST::Wire>(std::move(arg)));
            },
            process_decl(std::move(id), field_type));
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
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, field)                  \
  ASSERT(verilog_json.count(field) == 0,                                       \
         std::string("Can not include ") + std::string(field) +                \
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
std::unique_ptr<vAST::AbstractModule>
Passes::Verilog::compileStringBodyModule(json verilog_json, std::string name,
                                         Module *module) {
  std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
  for (auto port_str :
       verilog_json["interface"].get<std::vector<std::string>>()) {
    if (this->verilator_debug) {
        // FIXME: Hack to get comment into port name, we need to design a way
        // to attach comments to expressions
        port_str += "/*verilator public*/";
    }
    ports.push_back(std::make_unique<vAST::StringPort>(port_str));
  }
  vAST::Parameters parameters;
  std::set<std::string> parameters_seen;
  // The wrap primitive has an unused parameter "type" that we ignore
  if (module->isGenerated() && module->getGenerator()->getName() != "wrap") {
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
        parameters.push_back(
            std::pair(std::make_unique<vAST::Identifier>(parameter.first),
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
  std::string definition;
  if (this->verilator_debug &&
      verilog_json.count("verilator_debug_definition")) {
    definition = verilog_json["verilator_debug_definition"].get<std::string>();
  } else {
    definition = verilog_json["definition"].get<std::string>();
  }
  return std::make_unique<vAST::StringBodyModule>(
      name, std::move(ports), definition, std::move(parameters));
}

// Compile a CoreIR record type corresponding to the interface of a module with
// flattened types into a vector of vAST Ports
std::vector<std::unique_ptr<vAST::AbstractPort>>
Passes::Verilog::compilePorts(RecordType *record_type) {
  std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
  for (auto field : record_type->getFields()) {
    Type *field_type = record_type->getRecord().at(field);
    std::unique_ptr<vAST::Identifier> name =
        std::make_unique<vAST::Identifier>(field);

    vAST::Direction verilog_direction;
    if (field_type->isInput()) {
      verilog_direction = vAST::INPUT;
    } else if (field_type->isOutput()) {
      verilog_direction = vAST::OUTPUT;
    } else if (field_type->isInOut()) {
      verilog_direction = vAST::INOUT;
    } else {
      ASSERT(false, "Not implemented for type = " + toString(field_type));
    }
    std::unique_ptr<vAST::Port> port =
        std::make_unique<vAST::Port>(process_decl(std::move(name), field_type),
                                     verilog_direction, vAST::WIRE);
    if (this->verilator_debug) {
      port = vAST::AddComment(std::move(port), "verilator public");
    }
    ports.push_back(std::move(port));
  };
  return ports;
}

// Helper class to use a pair of the form <instance_name, port_name> as a key
// for a map. Chosen over just using std::pair because it seems like it makes
// it easier to read the code.
class ConnMapKey {
public:
  std::string instance_name;
  std::string port_name;
  ConnMapKey(std::string instance_name, std::string port_name)
      : instance_name(instance_name), port_name(port_name){};
  bool operator==(const ConnMapKey &other) const {
    return instance_name == other.instance_name && port_name == other.port_name;
  }
  bool operator<(const ConnMapKey &other) const {
    return (instance_name + port_name) <
           (other.instance_name + other.port_name);
  }
  std::size_t operator()(const ConnMapKey &k) const {
    return std::hash<std::string>()(instance_name + port_name);
  }
};

// An entry in the connection map contains a source wireable (driving the port
// denoted by the key). It also contains an index in the case of a driver
// connecting to a sub element of the port.  Metadata is used to generate debug
// info
class ConnMapEntry {
public:
  Wireable *source;
  int index;
  json& metadata;
  ConnMapEntry(Wireable *source, int index, json& metadata) : source(source),
    index(index), metadata(metadata){};
};

// Builds a map from pairs of strings of the form <instance_name, port_name>
// to the source Wireable(s) which will be used to generate the verilog
// identifier corresponding to the wire connecting the two entities
//
// connection_map entries are a vector of ConnMapEntries to handle the case
// when multiple signals drive an input to an instance (e.g. the input is an
// array of 3 bits, and each bit is connected to a 1-bit driver).  In this
// case, each entry stores the index that it drives.
std::map<ConnMapKey, std::vector<ConnMapEntry>>
build_connection_map(CoreIR::ModuleDef *definition,
                     std::map<std::string, Instance *> instances) {
  std::vector<Connection> connections = definition->getSortedConnections();
  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map;
  for (auto connection : connections) {
    // Check if this is connected to an instance to an instance input, if
    // it is, populate the entry in the connection map
    for (auto instance : instances) {
      if (connection.first->getTopParent() == instance.second &&
          connection.first->getType()->isInput()) {
        SelectPath first_sel_path = connection.first->getSelectPath();
        int index = 0;
        if (first_sel_path.size() > 2) {
          index = std::stoi(first_sel_path[2]);
        }
        connection_map[ConnMapKey(instance.first, first_sel_path[1])].push_back(
            ConnMapEntry(connection.second, index,
                definition->getMetaData(connection.first, connection.second)));
      } else if (connection.second->getTopParent() == instance.second &&
                 connection.second->getType()->isInput()) {
        SelectPath second_sel_path = connection.second->getSelectPath();
        int index = 0;
        if (second_sel_path.size() > 2) {
          index = std::stoi(second_sel_path[2]);
        }
        connection_map[ConnMapKey(instance.first, second_sel_path[1])]
            .push_back(ConnMapEntry(connection.first, index,
                        definition->getMetaData(connection.first,
                            connection.second)));
      }
    }
    // Also check if the connection is driving a self port, which will be
    // wired up at the end
    if (connection.first->getSelectPath()[0] == "self" &&
        connection.first->getType()->isInput()) {
      SelectPath first_sel_path = connection.first->getSelectPath();
      int index = 0;
      if (first_sel_path.size() > 2) {
        index = std::stoi(first_sel_path[2]);
      }
      connection_map[ConnMapKey("self", first_sel_path[1])].push_back(
          ConnMapEntry(connection.second, index,
              definition->getMetaData(connection.first, connection.second)));
    } else if (connection.second->getSelectPath()[0] == "self" &&
               connection.second->getType()->isInput()) {
      SelectPath second_sel_path = connection.second->getSelectPath();
      int index = 0;
      if (second_sel_path.size() > 2) {
        index = std::stoi(second_sel_path[2]);
      }
      connection_map[ConnMapKey("self", second_sel_path[1])].push_back(
          ConnMapEntry(connection.first, index,
              definition->getMetaData(connection.first, connection.second)));
    }
  }
  return connection_map;
}

// Join select path fields by "_" (ignoring intial self if present)
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Index>>
convert_to_verilog_connection(Wireable *value) {
  SelectPath select_path = value->getSelectPath();
  if (select_path.front() == "self") {
    select_path.pop_front();
  }
  std::string connection_name = "";
  for (uint i = 0; i < select_path.size(); i++) {
    auto item = select_path[i];
    if (isNumber(item)) {
      ASSERT(i == select_path.size() - 1, "Assumed flattened types have array index as last element in select path");
      return std::make_unique<vAST::Index>(vAST::make_id(connection_name),
                                           vAST::make_num(item));
    } else if (connection_name != "") {
      connection_name += "_";
    }
    connection_name += item;
  }
  return vAST::make_id(connection_name);
}

void process_connection_debug_metadata(
        ConnMapEntry entry, 
        std::string verilog_conn_str,
        std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                                 std::unique_ptr<vAST::Declaration>>> &body,
        std::string source_str) {
  if (entry.metadata.count("filename") > 0) {
    std::string debug_str = "Connection `(" + source_str + ", " +
        verilog_conn_str +")` created at " +
        entry.metadata["filename"].get<std::string>();
    if (entry.metadata.count("lineno") > 0) {
      debug_str += ":" + entry.metadata["lineno"].get<std::string>();
    }
    body.push_back(std::make_unique<vAST::SingleLineComment>(debug_str));
  }
}

// If it is not a bulk connection, create a concat node and wire up the inputs
// by index
std::unique_ptr<vAST::Concat>
convert_non_bulk_connection_to_concat(std::vector<ConnMapEntry> entries,
        std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                                 std::unique_ptr<vAST::Declaration>>> &body,
        std::string debug_prefix) {
  std::vector<std::unique_ptr<vAST::Expression>> args;
  args.resize(entries.size());
  for (auto entry : entries) {
    std::unique_ptr<vAST::Expression> verilog_conn =
        convert_to_expression(convert_to_verilog_connection(entry.source));
    process_connection_debug_metadata(entry, verilog_conn->toString(), body,
            debug_prefix + "[" + std::to_string(entry.index) + "]");
    args[entry.index] = std::move(verilog_conn);
  }
  std::reverse(args.begin(), args.end());
  return std::make_unique<vAST::Concat>(std::move(args));
}

// For each output of the current module definition, emit a statement of the
// form: `assign <output> = <driver(s)>;`
void assign_module_outputs(
    RecordType *record_type,
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>> &body,
    std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map) {
  for (auto field : record_type->getFields()) {
    Type *field_type = record_type->getRecord().at(field);
    if (field_type->isInput()) {
      continue;
    }
    auto entries = connection_map[ConnMapKey("self", field)];
    if (entries.size() == 0) {
      continue;
    } else if (entries.size() > 1) {
      std::unique_ptr<vAST::Concat> concat =
          convert_non_bulk_connection_to_concat(entries, body, field);
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
          std::make_unique<vAST::Identifier>(field), std::move(concat)));
    } else {
      std::unique_ptr<vAST::Expression> verilog_conn =
          convert_to_expression(convert_to_verilog_connection(entries[0].source));
      process_connection_debug_metadata(entries[0], verilog_conn->toString(), body,
              field);
      // Regular (possibly bulk) connection
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
          std::make_unique<vAST::Identifier>(field),
          std::move(verilog_conn)
      ));
    }
  }
}

// assign inout ports
void assign_inouts(
    std::vector<Connection> connections,
    std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                             std::unique_ptr<vAST::Declaration>>> &body) {
  for (auto connection : connections) {
    if (connection.first->getType()->isInOut() ||
        connection.second->getType()->isInOut()) {
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
              convert_to_assign_target(convert_to_verilog_connection(connection.first)),
              convert_to_expression(convert_to_verilog_connection(connection.second))
       ));
    };
  };
}


// Traverses the instance map and creates a vector of module instantiations
// using connection_map to wire up instance ports
std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                         std::unique_ptr<vAST::Declaration>>>
compile_module_body(RecordType *module_type,
                    CoreIR::ModuleDef *definition,
                    bool _inline) {
  std::map<std::string, Instance *> instances = definition->getInstances();

  std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                           std::unique_ptr<vAST::Declaration>>>
      body = declare_connections(instances);

  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map =
      build_connection_map(definition, instances);

  for (auto instance : instances) {
    Module *instance_module = instance.second->getModuleRef();
    std::string module_name = instance_module->getName();
    if (instance_module->isGenerated()) {
      if (instance_module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json =
            instance_module->getGenerator()->getMetaData()["verilog"];
        module_name = make_name(module_name, verilog_json);
      } else {
        module_name = instance_module->getLongName();
      }
    } else if (instance_module->getMetaData().count("verilog") > 0) {
      json verilog_json = instance_module->getMetaData()["verilog"];
      module_name = make_name(module_name, verilog_json);
    }
    vAST::Parameters instance_parameters;
    std::string instance_name = instance.first;

    if (instance.second->getMetaData().count("filename") > 0) {
      std::string debug_str = "Instance `" + instance_name + "` created at " +
        instance.second->getMetaData()["filename"].get<std::string>();
      if (instance.second->getMetaData().count("lineno") > 0) {
        debug_str += ":" + instance.second->getMetaData()["lineno"].get<std::string>();
      }
      body.push_back(std::make_unique<vAST::SingleLineComment>(debug_str));
    }

    std::unique_ptr<vAST::Connections> verilog_connections =
        std::make_unique<vAST::Connections>();
    RecordType *record_type = cast<RecordType>(instance_module->getType());
    for (auto field : record_type->getFields()) {
      Type *field_type = record_type->getRecord().at(field);
      if (!field_type->isInput()) {
        // output or inout, emit wire name
        verilog_connections->insert(
            field,
            std::make_unique<vAST::Identifier>(instance.first + "_" + field));
        continue;
      }
      auto entries = connection_map[ConnMapKey(instance.first, field)];
      if (entries.size() == 0) {
        continue;
      } else if (entries.size() > 1) {
        std::unique_ptr<vAST::Concat> concat =
            convert_non_bulk_connection_to_concat(entries, body, 
                instance_name + "." + field);
        verilog_connections->insert(field, std::move(concat));
        // Otherwise we just use the entry in the connection map
      } else {
        std::unique_ptr<vAST::Expression> verilog_conn =
            convert_to_expression(convert_to_verilog_connection(entries[0].source));
        process_connection_debug_metadata(entries[0], verilog_conn->toString(), body,
                instance_name + "." + field);
        verilog_connections->insert(field, std::move(verilog_conn));
      }
    }
    // Handle module arguments
    if (instance.second->hasModArgs()) {
      for (auto parameter : instance.second->getModArgs()) {
        instance_parameters.push_back(
            std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                      convert_value(parameter.second)));
      }
    }
    // Handle generator arguments
    if (instance_module->isGenerated() &&
        instance_module->getGenerator()->getMetaData().count("verilog") > 0 &&
        // Ignore wrap "type" parameter
        instance_module->getGenerator()->getName() != "wrap") {
      for (auto parameter : instance.second->getModuleRef()->getGenArgs()) {
        instance_parameters.push_back(
            std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                      convert_value(parameter.second)));
      }
    }
    std::unique_ptr<vAST::StructuralStatement> statement;
    if (can_inline_binary_op(instance_module, _inline)) {
        statement = inline_binary_op(instance, std::move(verilog_connections));
    } else if (can_inline_unary_op(instance_module, _inline)) {
        statement = inline_unary_op(instance, std::move(verilog_connections));
    } else if (can_inline_mux_op(instance_module, _inline)) {
        statement = inline_mux_op(instance, std::move(verilog_connections));
    } else if (can_inline_const_op(instance_module, _inline)) {
        ASSERT(instance_parameters[0].first->value == "value", 
            "expected first param to be const value");
        statement = std::make_unique<vAST::ContinuousAssign>(
            std::make_unique<vAST::Identifier>(instance.first + "_out"),
            std::move(instance_parameters[0].second));
    } else if (can_inline_slice_op(instance_module, _inline)) {
        ASSERT(instance_parameters[0].first->value == "hi", 
            "expected first param to be hi");
        ASSERT(instance_parameters[1].first->value == "lo", 
            "expected second param to be lo");
        statement = std::make_unique<vAST::ContinuousAssign>(
            std::make_unique<vAST::Identifier>(instance.first + "_out"),
            std::make_unique<vAST::Slice>(
                verilog_connections->at("in"),
                vAST::make_binop(
                    std::move(instance_parameters[0].second), 
                    vAST::BinOp::SUB,
                    vAST::make_num("1")
                ),
                std::move(instance_parameters[1].second)
            ));
    } else {
        statement = std::make_unique<vAST::ModuleInstantiation>(
            module_name, std::move(instance_parameters), instance_name,
            std::move(verilog_connections));
    }
    body.push_back(std::move(statement));
  }
  // Wire the outputs of the module and inout connections
  assign_module_outputs(module_type, body, connection_map);
  assign_inouts(definition->getSortedConnections(), body);
  return body;
}

// Convert CoreIR paraemters into vAST Parameters
vAST::Parameters compile_params(Module *module) {
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
        parameters.push_back(
            std::pair(std::make_unique<vAST::Identifier>(parameter.first),
                      std::make_unique<vAST::NumericLiteral>("1")));
      }
    }
  }
  return parameters;
}

void Passes::Verilog::compileModule(Module *module) {
  if ((module->getMetaData().count("inline_verilog") > 0) &&
      (module->getMetaData().count("verilog") > 0)) {
    LOG(WARN) << "WARNING: " + module->getRefName() + " has both `inline_verilog` and `verilog` metadata, `inline_verilog` will be ignored";
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    if (module->hasPrimitiveExpressionLambda() &&
            is_inlined(verilog_json["primitive_type"], module->getName()) &&
            this->_inline) {
        // Module is inlined
        return;
    }
    if (verilog_json.count("verilog_string") > 0) {
      // module is defined by a verilog string, we just emit the entire
      // string
      modules.push_back(std::make_pair(module->getName(),
                                       compile_string_module(verilog_json)));
    } else {
      std::string name = make_name(module->getName(), verilog_json);
      modules.push_back(std::make_pair(
          name, compileStringBodyModule(verilog_json, name, module)));
    }
    return;
  }
  if (module->isGenerated() &&
      module->getGenerator()->getMetaData().count("verilog") > 0) {
    // This module is an instance of generator defined as a parametrized
    // verilog module
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    if (module->getGenerator()->hasPrimitiveExpressionLambda() &&
            is_inlined(verilog_json["primitive_type"], module->getName()) &&
            this->_inline) {
        // Module is inlined
        return;
    }
    std::string name = make_name(module->getName(), verilog_json);

    modules.push_back(std::make_pair(
        name, compileStringBodyModule(verilog_json, name, module)));

    // We only need to compile the verilog generator once, even though
    // there may be multiple instances of the generator represented as
    // different modules. We populate this set so that instance graph pass
    // can filter out other instnaces of the generator.
    verilog_generators_seen.insert(module->getGenerator());
    return;
  }
  if (!(module->hasDef() || module->hasVerilogDef())) {
    extern_modules.push_back(module);
    return;
  }
  std::vector<std::unique_ptr<vAST::AbstractPort>> ports =
      compilePorts(cast<RecordType>(module->getType()));

  ModuleDef *definition = module->getDef();
  std::vector<std::variant<std::unique_ptr<vAST::StructuralStatement>,
                           std::unique_ptr<vAST::Declaration>>>
      body;
  if (module->hasDef()) {
      body = compile_module_body(module->getType(), definition,
                                 this->_inline);
  }

  if (module->getMetaData().count("filename") > 0) { 
    std::string debug_str = "Module `" + module->getName() + "` defined at " +
      module->getMetaData()["filename"].get<std::string>();
    if (module->getMetaData().count("lineno") > 0) {
      debug_str += ":" + module->getMetaData()["lineno"].get<std::string>();
    }
    body.insert(
      body.begin(), std::make_unique<vAST::SingleLineComment>(debug_str));
  }



  // Temporary support for inline verilog
  // See https://github.com/rdaly525/coreir/pull/823 for context
  if (module->getMetaData().count("inline_verilog") > 0) {
    std::string inline_str = module->getMetaData()["inline_verilog"].get<std::string>();
    body.push_back(std::make_unique<vAST::InlineVerilog>(inline_str));
  }

  vAST::Parameters parameters = compile_params(module);

  std::string name = module->getLongName();
  std::unique_ptr<vAST::AbstractModule> verilog_module =
      std::make_unique<vAST::Module>(name, std::move(ports), std::move(body),
                                     std::move(parameters));

  if (this->_inline) {
      vAST::AssignInliner transformer;
      verilog_module = transformer.visit(std::move(verilog_module));
  }
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

void Passes::Verilog::writeToFiles(const std::string &dir,
                                   std::unique_ptr<std::string> product_file) {
  std::vector<std::string> products;
  for (auto &module : modules) {
    const std::string filename = module.first + ".v";
    products.push_back(filename);
    const std::string full_filename = dir + "/" + filename;
    std::ofstream output_file(full_filename);
    if (!output_file.is_open()) {
      throw std::runtime_error("Could not open file: " + full_filename);
    }
    output_file << module.second->toString() << std::endl;
    output_file.close();
  }
  // Write out the product list, if requested.
  if (!product_file)
    return;
  std::ofstream fout(*product_file);
  ASSERT(fout.is_open(), "Cannot open file: " + *product_file);
  for (const auto &product : products) {
    fout << product << "\n";
  }
  fout.close();
}

} // namespace CoreIR
