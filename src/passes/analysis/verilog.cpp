#include "coreir/passes/analysis/verilog.h"
#include <fstream>
#include <regex>
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/passes/analysis/verilog/inline_utils.hpp"
#include "coreir/tools/cxxopts.h"
#include "verilogAST/assign_inliner.hpp"
#include "verilogAST/transformer.hpp"

namespace vAST = verilogAST;

// Unpack variant type and convert to parent type Expression
std::unique_ptr<vAST::Expression> convert_to_expression(
  std::variant<
    std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::Attribute>,
    std::unique_ptr<vAST::Index>,
    std::unique_ptr<vAST::Slice>> value) {
  return std::visit(
    [](auto&& value) -> std::unique_ptr<vAST::Expression> {
      return std::move(value);
    },
    value);
}

// Checks runtype type of expression and return assign target or error
std::variant<
  std::unique_ptr<vAST::Identifier>,
  std::unique_ptr<vAST::Index>,
  std::unique_ptr<vAST::Slice>>
convert_to_assign_target(std::variant<
                         std::unique_ptr<vAST::Identifier>,
                         std::unique_ptr<vAST::Attribute>,
                         std::unique_ptr<vAST::Index>,
                         std::unique_ptr<vAST::Slice>> value) {
  return std::visit(
    [](auto&& value) -> std::variant<
                       std::unique_ptr<vAST::Identifier>,
                       std::unique_ptr<vAST::Index>,
                       std::unique_ptr<vAST::Slice>> {
      if (auto ptr = dynamic_cast<vAST::Identifier*>(value.get())) {
        value.release();
        return std::unique_ptr<vAST::Identifier>(ptr);
      }
      if (auto ptr = dynamic_cast<vAST::Index*>(value.get())) {
        value.release();
        return std::unique_ptr<vAST::Index>(ptr);
      }
      if (auto ptr = dynamic_cast<vAST::Slice*>(value.get())) {
        value.release();
        return std::unique_ptr<vAST::Slice>(ptr);
      }
      throw std::runtime_error("Cannot convert Attribute to assign target");
      return std::unique_ptr<vAST::Identifier>{};  // nullptr
    },
    std::move(value));
}

bool is_wire_module(CoreIR::Module* mod) {
  if (mod->getNamespace()->getName() == "corebit" && mod->getName() == "wire")
    return true;
  if (!mod->isGenerated()) return false;
  CoreIR::Generator* gen = mod->getGenerator();
  return gen->getName() == "wire" &&
    (gen->getNamespace()->getName() == "coreir" ||
     gen->getNamespace()->getName() == "mantle");
}

bool check_inline_verilog_wire_metadata(CoreIR::Instance* inst) {
  json metadata = inst->getMetaData();
  if (metadata.count("inline_verilog_wire") == 0) return false;
  return metadata["inline_verilog_wire"].get<bool>();
}

namespace CoreIR {

void Passes::Verilog::initialize(int argc, char** argv) {
  cxxopts::Options options("verilog", "translates coreir graph to verilog");
  options.add_options()("i,inline", "Inline verilog modules if possible")(
    "y,verilator_debug",
    "Mark IO and intermediate wires as /*verilator_public*/")(
    "w,disable-width-cast",
    "Omit width cast in generated verilog when using inline");
  auto opts = options.parse(argc, argv);
  if (opts.count("i")) { this->_inline = true; }
  if (opts.count("y")) { this->verilator_debug = true; }
  if (opts.count("w")) { this->disable_width_cast = true; }
}

// Helper function that prepends a prefix contained in json metadata if it
// exists
std::string make_name(std::string name, json metadata) {
  if (metadata.count("prefix") > 0) {
    name = metadata["prefix"].get<std::string>() + name;
  }
  return name;
}

std::unique_ptr<vAST::Expression> convert_mem_init_param_value(
  Value* value,
  int width) {
  // Assumes json list of ints
  json json_value = dyn_cast<ConstJson>(value)->get();
  ASSERT(json_value != NULL, "Got non-json value for mem init");
  ASSERT(json_value.is_array(), "Got non-json array for mem init");
  std::vector<std::unique_ptr<vAST::Expression>> concat_args;
  for (auto& element : json_value) {
    ASSERT(
      element.is_number(),
      "Got non-number for json array element in mem init");
    concat_args.push_back(std::make_unique<vAST::NumericLiteral>(
      std::to_string(element.get<unsigned long long>()),
      width));
  }
  std::reverse(concat_args.begin(), concat_args.end());

  return std::make_unique<vAST::Concat>(std::move(concat_args));
}

// Converts a CoreIR `Value` type into a Verilog literal
std::unique_ptr<vAST::Expression> convert_value(Value* value) {
  if (auto arg_value = dyn_cast<Arg>(value)) {
    return std::make_unique<vAST::Identifier>(arg_value->getField());
  }
  else if (auto int_value = dyn_cast<ConstInt>(value)) {
    return std::make_unique<vAST::NumericLiteral>(int_value->toString());
  }
  else if (auto bool_value = dyn_cast<ConstBool>(value)) {
    return std::make_unique<vAST::NumericLiteral>(
      std::to_string(uint(bool_value->get())),
      1,
      false,
      vAST::BINARY);
  }
  else if (auto bit_vector_value = dyn_cast<ConstBitVector>(value)) {
    BitVector bit_vector = bit_vector_value->get();
    return std::make_unique<vAST::NumericLiteral>(
      bit_vector.hex_digits(),
      bit_vector.bitLength(),
      false,
      vAST::HEX,
      true);
  }
  else if (auto string_value = dyn_cast<ConstString>(value)) {
    return std::make_unique<vAST::String>(string_value->toString());
  }
  coreir_unreachable();
}

// unpack named types to get the raw type (so we can check that it's a
// bit), iteratively because perhaps you can name and named type?
// This is just a safety check for internal code, to improve performance,
// we could guard this assert logic behind a macro
Type* get_raw_type(Type* type) {
  while (isa<NamedType>(type)) { type = cast<NamedType>(type)->getRaw(); }
  return type;
}

// Given a signal named `id` and a type `type`, wrap the signal name in a
// `Vector` node if the signal is of type Array
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Vector>>
process_decl(std::unique_ptr<vAST::Identifier> id, Type* type) {
  if (isa<ArrayType>(type)) {
    ArrayType* array_type = cast<ArrayType>(type);
    Type* internal_type = get_raw_type(array_type->getElemType());
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

void make_decl(
  std::string name,
  Type* type,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& declarations,
  bool is_reg) {
  std::unique_ptr<vAST::Identifier> id = std::make_unique<vAST::Identifier>(
    name);
  // Can't find a simple way to "convert" a variant type to a
  // superset, so we just manually unpack it to call the Wire
  // constructor
  std::visit(
    [&](auto&& arg) -> void {
      std::unique_ptr<vAST::Declaration> decl;
      if (is_reg) { decl = std::make_unique<vAST::Reg>(std::move(arg)); }
      else {
        decl = std::make_unique<vAST::Wire>(std::move(arg));
      }
      declarations.push_back(std::move(decl));
    },
    process_decl(std::move(id), type));
}

// Given a map of instances, return a vector of containing declarations for all
// the output ports of each instance.  We return a vector of a variant type for
// compatibility with the module AST node constructor, even though we only ever
// create Wire nodes.
std::vector<std::variant<
  std::unique_ptr<vAST::StructuralStatement>,
  std::unique_ptr<vAST::Declaration>>>
declare_connections(std::map<std::string, Instance*> instances, bool _inline) {
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
    declarations;
  for (auto instance : instances) {
    if (is_wire_module(instance.second->getModuleRef()) && _inline) {
      // Emit inline wire
      Type* type = cast<RecordType>(instance.second->getModuleRef()->getType())
                     ->getRecord()
                     .at("in");
      make_decl(instance.first, type, declarations, false);
      continue;
    }
    RecordType* record_type = cast<RecordType>(
      instance.second->getModuleRef()->getType());
    bool is_reg = _inline && is_muxn(instance.second->getModuleRef());
    for (auto field : record_type->getFields()) {
      Type* field_type = record_type->getRecord().at(field);
      if (!field_type->isInput()) {
        make_decl(
          instance.first + "_" + field,
          field_type,
          declarations,
          is_reg);
      }
    }
  }
  return declarations;
}

// Compiles a module defined with `verilog_string` in the `verilog` metadata
// field
std::unique_ptr<vAST::AbstractModule> compile_string_module(json verilog_json) {
  // Ensure that if the field verilog_string is included that the
  // remaining fields are not included.
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(verilog_json, field)                  \
  ASSERT(                                                                      \
    verilog_json.count(field) == 0,                                            \
    std::string("Can not include ") + std::string(field) +                     \
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
std::unique_ptr<vAST::AbstractModule> Passes::Verilog::compileStringBodyModule(
  json verilog_json,
  std::string name,
  Module* module) {
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
      parameters.push_back(std::pair(
        std::make_unique<vAST::Identifier>(parameter.first),
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
    if (
      module->isGenerated() && module->getGenerator()->getName() == "mem" &&
      module->getGenerator()->getNamespace()->getName() == "coreir" &&
      parameter.first == "init") {
      // init param is handled using a parameter statement in verilog string
      // defn
      continue;
    }
    if (parameters_seen.count(parameter.first) == 0) {
      // Old coreir backend defaults these (genparams without
      // defaults) to 0
      parameters.push_back(std::pair(
        std::make_unique<vAST::Identifier>(parameter.first),
        std::make_unique<vAST::NumericLiteral>("1")));
    }
  }
  std::string definition;
  if (
    this->verilator_debug && verilog_json.count("verilator_debug_definition")) {
    definition = verilog_json["verilator_debug_definition"].get<std::string>();
  }
  else {
    definition = verilog_json["definition"].get<std::string>();
  }
  return std::make_unique<vAST::StringBodyModule>(
    name,
    std::move(ports),
    definition,
    std::move(parameters));
}

// Compile a CoreIR record type corresponding to the interface of a module with
// flattened types into a vector of vAST Ports
std::vector<std::unique_ptr<vAST::AbstractPort>> Passes::Verilog::compilePorts(
  RecordType* record_type) {
  std::vector<std::unique_ptr<vAST::AbstractPort>> ports;
  for (auto field : record_type->getFields()) {
    Type* field_type = record_type->getRecord().at(field);
    std::unique_ptr<vAST::Identifier> name = std::make_unique<vAST::Identifier>(
      field);

    vAST::Direction verilog_direction;
    if (field_type->isInput()) { verilog_direction = vAST::INPUT; }
    else if (field_type->isOutput()) {
      verilog_direction = vAST::OUTPUT;
    }
    else if (field_type->isInOut()) {
      verilog_direction = vAST::INOUT;
    }
    else {
      ASSERT(false, "Not implemented for type = " + toString(field_type));
    }
    std::unique_ptr<vAST::Port> port = std::make_unique<vAST::Port>(
      process_decl(std::move(name), field_type),
      verilog_direction,
      vAST::WIRE);
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
      : instance_name(instance_name),
        port_name(port_name){};
  bool operator==(const ConnMapKey& other) const {
    return instance_name == other.instance_name && port_name == other.port_name;
  }
  bool operator<(const ConnMapKey& other) const {
    return (instance_name + port_name) <
      (other.instance_name + other.port_name);
  }
  std::size_t operator()(const ConnMapKey& k) const {
    return std::hash<std::string>()(instance_name + port_name);
  }
};

// An entry in the connection map contains a source wireable (driving the port
// denoted by the key). It also contains an index in the case of a driver
// connecting to a sub element of the port.  Metadata is used to generate debug
// info
class ConnMapEntry {
 public:
  Wireable* source;
  int index;
  json& metadata;
  ConnMapEntry(Wireable* source, int index, json& metadata)
      : source(source),
        index(index),
        metadata(metadata){};
};

// Builds a map from pairs of strings of the form <instance_name, port_name>
// to the source Wireable(s) which will be used to generate the verilog
// identifier corresponding to the wire connecting the two entities
//
// connection_map entries are a vector of ConnMapEntries to handle the case
// when multiple signals drive an input to an instance (e.g. the input is an
// array of 3 bits, and each bit is connected to a 1-bit driver).  In this
// case, each entry stores the index that it drives.
std::map<ConnMapKey, std::vector<ConnMapEntry>> build_connection_map(
  CoreIR::ModuleDef* definition,
  std::map<std::string, Instance*> instances) {
  std::vector<Connection> connections = definition->getSortedConnections();
  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map;
  for (auto connection : connections) {
    // Check if this is connected to an instance to an instance input, if
    // it is, populate the entry in the connection map
    for (auto instance : instances) {
      if (
        connection.first->getTopParent() == instance.second &&
        connection.first->getType()->isInput()) {
        SelectPath first_sel_path = connection.first->getSelectPath();
        int index = 0;
        if (first_sel_path.size() > 2) { index = std::stoi(first_sel_path[2]); }
        connection_map[ConnMapKey(instance.first, first_sel_path[1])].push_back(
          ConnMapEntry(
            connection.second,
            index,
            definition->getMetaData(connection.first, connection.second)));
      }
      else if (
        connection.second->getTopParent() == instance.second &&
        connection.second->getType()->isInput()) {
        SelectPath second_sel_path = connection.second->getSelectPath();
        int index = 0;
        if (second_sel_path.size() > 2) {
          index = std::stoi(second_sel_path[2]);
        }
        connection_map[ConnMapKey(instance.first, second_sel_path[1])]
          .push_back(ConnMapEntry(
            connection.first,
            index,
            definition->getMetaData(connection.first, connection.second)));
      }
    }
    // Also check if the connection is driving a self port, which will be
    // wired up at the end
    if (
      connection.first->getSelectPath()[0] == "self" &&
      connection.first->getType()->isInput()) {
      SelectPath first_sel_path = connection.first->getSelectPath();
      int index = 0;
      if (first_sel_path.size() > 2) { index = std::stoi(first_sel_path[2]); }
      connection_map[ConnMapKey("self", first_sel_path[1])].push_back(
        ConnMapEntry(
          connection.second,
          index,
          definition->getMetaData(connection.first, connection.second)));
    }
    else if (
      connection.second->getSelectPath()[0] == "self" &&
      connection.second->getType()->isInput()) {
      SelectPath second_sel_path = connection.second->getSelectPath();
      int index = 0;
      if (second_sel_path.size() > 2) { index = std::stoi(second_sel_path[2]); }
      connection_map[ConnMapKey("self", second_sel_path[1])].push_back(
        ConnMapEntry(
          connection.first,
          index,
          definition->getMetaData(connection.first, connection.second)));
    }
  }
  return connection_map;
}

// Join select path fields by "_" (ignoring intial self if present)
std::variant<
  std::unique_ptr<vAST::Identifier>,
  std::unique_ptr<vAST::Attribute>,
  std::unique_ptr<vAST::Index>,
  std::unique_ptr<vAST::Slice>>
convert_to_verilog_connection(Wireable* value, bool _inline) {
  SelectPath select_path = value->getSelectPath();
  if (select_path.front() == "self") { select_path.pop_front(); }
  Wireable* parent = value->getTopParent();
  if (
    _inline && parent->getKind() == Wireable::WK_Instance &&
    is_wire_module(cast<Instance>(parent)->getModuleRef())) {
    // Use instance name as wire name
    select_path.pop_front();
    select_path[0] = parent->toString();
  }

  // Used to track the current select so we can see if it's an instance
  Wireable* curr_wireable = value->getTopParent();

  std::variant<
    std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::Attribute>,
    std::unique_ptr<vAST::Slice>>
    curr_node;
  for (uint i = 0; i < select_path.size(); i++) {
    auto item = select_path[i];
    if (isNumber(item)) {
      ASSERT(
        i == select_path.size() - 1,
        "Assumed flattened types have array index as last element "
        "in select path");
      return std::make_unique<vAST::Index>(
        std::move(curr_node),
        vAST::make_num(item));
    }
    else if (isSlice(item)) {
      int low;
      int high;
      std::tie(low, high) = parseSlice(item);
      curr_node = std::make_unique<vAST::Slice>(
        std::visit(
          [](auto&& value) -> std::unique_ptr<vAST::Expression> {
            return std::move(value);
          },
          curr_node),
        vAST::make_num(std::to_string(high - 1)),
        vAST::make_num(std::to_string(low)));
    }
    else {
      if (i > 0) {
        // advance to next wireable if we're past the first select
        curr_wireable = curr_wireable->sel(item);
      }
      // Handle hierarchical select of instance
      if (isa<InstanceSelect>(curr_wireable)) {
        // First node should have been a normal instance
        ASSERT(
          std::visit(
            [](auto&& node) -> bool { return node != NULL; },
            curr_node),
          "Expected non-null node for hierarchical reference");
        // We need to pack into restricted type for attribute expression (can't
        // attribute a Slice)
        std::variant<
          std::unique_ptr<vAST::Identifier>,
          std::unique_ptr<vAST::Attribute>>
          attr_expr = std::visit(
            [](auto&& value) -> std::variant<
                               std::unique_ptr<vAST::Identifier>,
                               std::unique_ptr<vAST::Attribute>> {
              if (auto ptr = dynamic_cast<vAST::Identifier*>(value.get())) {
                value.release();
                return std::unique_ptr<vAST::Identifier>(ptr);
              }
              if (auto ptr = dynamic_cast<vAST::Attribute*>(value.get())) {
                value.release();
                return std::unique_ptr<vAST::Attribute>(ptr);
              }
              throw std::runtime_error(
                "Found unexpected slice inside hierarchical select");
            },
            std::move(curr_node));

        // .substr(1) to skip ; prefix
        for (auto inst : splitString<SelectPath>(item.substr(1), ';')) {
          // Construct nested attribute node
          attr_expr = std::make_unique<vAST::Attribute>(
            std::move(attr_expr),
            inst);
        }
        // Should be an attribute since we assume theres at least one
        // hierarchical select if we're in this code path (will runtime error if
        // otherwise)
        curr_node = std::move(
          std::get<std::unique_ptr<vAST::Attribute>>(attr_expr));
      }
      else {
        if (std::visit(
              [](auto&& node) -> bool { return node == NULL; },
              curr_node)) {
          // first level select, make an id
          curr_node = vAST::make_id(item);
        }
        else if (std::holds_alternative<std::unique_ptr<vAST::Attribute>>(
                   curr_node)) {
          // selecting off a hierarchical instance select
          curr_node = std::make_unique<vAST::Attribute>(
            std::move(std::get<std::unique_ptr<vAST::Attribute>>(curr_node)),
            item);
        }
        else {
          // append to current name being constructed
          ASSERT(
            std::holds_alternative<std::unique_ptr<vAST::Identifier>>(
              curr_node),
            "Expected ID");
          std::get<std::unique_ptr<vAST::Identifier>>(curr_node)->value += "_" +
            item;
        }
      }
    }
  }
  if (std::holds_alternative<std::unique_ptr<vAST::Identifier>>(curr_node)) {
    return std::get<std::unique_ptr<vAST::Identifier>>(std::move(curr_node));
  }
  if (std::holds_alternative<std::unique_ptr<vAST::Attribute>>(curr_node)) {
    return std::get<std::unique_ptr<vAST::Attribute>>(std::move(curr_node));
  }
  if (std::holds_alternative<std::unique_ptr<vAST::Slice>>(curr_node)) {
    return std::get<std::unique_ptr<vAST::Slice>>(std::move(curr_node));
  }
  throw std::runtime_error("Unreachable");
  return std::unique_ptr<vAST::Identifier>{};
}

void process_connection_debug_metadata(
  ConnMapEntry entry,
  std::string verilog_conn_str,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  std::string source_str) {
  if (entry.metadata.count("filename") > 0) {
    std::string debug_str = "Connection `(" + source_str + ", " +
      verilog_conn_str + ")` created at " +
      entry.metadata["filename"].get<std::string>();
    if (entry.metadata.count("lineno") > 0) {
      debug_str += ":" + entry.metadata["lineno"].get<std::string>();
    }
    body.push_back(std::make_unique<vAST::SingleLineComment>(debug_str));
  }
}

// If it is not a bulk connection, create a concat node and wire up the inputs
// by index
std::unique_ptr<vAST::Concat> convert_non_bulk_connection_to_concat(
  Type* field_type,
  std::vector<ConnMapEntry> entries,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  std::string debug_prefix,
  bool _inline) {

  std::vector<std::unique_ptr<vAST::Expression>> args;
  ASSERT(isa<ArrayType>(field_type), "Expected Array for concat connection");
  ArrayType* arr_type = cast<ArrayType>(field_type);
  args.resize(arr_type->getLen());

  for (auto entry : entries) {
    std::unique_ptr<vAST::Expression> verilog_conn = convert_to_expression(
      convert_to_verilog_connection(entry.source, _inline));
    process_connection_debug_metadata(
      entry,
      verilog_conn->toString(),
      body,
      debug_prefix + "[" + std::to_string(entry.index) + "]");
    args[entry.index] = std::move(verilog_conn);
  }

  // Verilog uses MSB -> LSB ordering
  std::reverse(args.begin(), args.end());

  // Remove empty cells, since there might be slices that only populate the
  // start index of the slice
  args.erase(
    std::remove_if(
      args.begin(),
      args.end(),
      [](std::unique_ptr<vAST::Expression>& arg) { return arg == NULL; }),
    args.end());

  return std::make_unique<vAST::Concat>(std::move(args));
}

// For each output of the current module definition, emit a statement of the
// form: `assign <output> = <driver(s)>;`
void assign_module_outputs(
  RecordType* record_type,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map,
  bool _inline) {
  for (auto field : record_type->getFields()) {
    Type* field_type = record_type->getRecord().at(field);
    if (field_type->isInput()) { continue; }
    auto entries = connection_map[ConnMapKey("self", field)];
    if (entries.size() == 0) { continue; }
    else if (entries.size() > 1) {
      std::unique_ptr<vAST::Concat>
        concat = convert_non_bulk_connection_to_concat(
          field_type,
          entries,
          body,
          field,
          _inline);
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
        std::make_unique<vAST::Identifier>(field),
        std::move(concat)));
    }
    else {
      std::unique_ptr<vAST::Expression> verilog_conn = convert_to_expression(
        convert_to_verilog_connection(entries[0].source, _inline));
      process_connection_debug_metadata(
        entries[0],
        verilog_conn->toString(),
        body,
        field);
      // Regular (possibly bulk) connection
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
        std::make_unique<vAST::Identifier>(field),
        std::move(verilog_conn)));
    }
  }
}

// assign inout ports
void assign_inouts(
  std::vector<Connection> connections,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  bool _inline) {
  for (auto connection : connections) {
    if (
      connection.first->getType()->isInOut() ||
      connection.second->getType()->isInOut()) {
      // coreir connections aren't assumed to be sorted, see
      // https://github.com/rdaly525/coreir/blob/f98c7bd8189d640ac078f6d60a1e86511bda4d64/src/ir/common.cpp#L84-L89),
      // so we sort them here
      // based on their lexical ordering so the code generation is consistent
      // (otherwise we can get flipped assignment statements)
      // note this is only an issue in the inout logic because the normal port
      // logic depends on the input/output relationship (output drives input) so
      // the order is enforced through other means
      Wireable* target = connection.first;
      Wireable* value = connection.second;
      bool order = SPComp(target->getSelectPath(), value->getSelectPath());
      if (!order) { std::swap(target, value); }
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
        convert_to_assign_target(
          convert_to_verilog_connection(target, _inline)),
        convert_to_expression(convert_to_verilog_connection(value, _inline))));
    };
  };
}

// Traverses the instance map and creates a vector of module instantiations
// using connection_map to wire up instance ports
std::vector<std::variant<
  std::unique_ptr<vAST::StructuralStatement>,
  std::unique_ptr<vAST::Declaration>>>
compile_module_body(
  RecordType* module_type,
  CoreIR::ModuleDef* definition,
  bool _inline,
  bool disable_width_cast,
  std::set<std::string>& wires) {
  std::map<std::string, Instance*> instances = definition->getInstances();

  std::vector<std::unique_ptr<vAST::StructuralStatement>> inline_verilog_body;

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
    body = declare_connections(instances, _inline);

  std::map<ConnMapKey, std::vector<ConnMapEntry>>
    connection_map = build_connection_map(definition, instances);

  for (auto instance : instances) {
    Module* instance_module = instance.second->getModuleRef();
    std::string module_name = instance_module->getLongName();
    if (instance_module->isGenerated()) {
      if (instance_module->getGenerator()->getMetaData().count("verilog") > 0) {
        json verilog_json = instance_module->getGenerator()
                              ->getMetaData()["verilog"];
        module_name = make_name(instance_module->getName(), verilog_json);
      }
    }
    else if (instance_module->getMetaData().count("verilog") > 0) {
      json verilog_json = instance_module->getMetaData()["verilog"];
      module_name = make_name(instance_module->getName(), verilog_json);
    }
    else if (instance_module->getMetaData().count("verilog_name") > 0) {
      // Allow user to provide specific module verilog name using metadata (e.g.
      // for ice40 primitives that are normally contained in the ice40
      // namespace, but we want to use their names without the ice40_ prefix
      // from longname)
      module_name = instance_module->getMetaData()["verilog_name"]
                      .get<std::string>();
    }
    vAST::Parameters instance_parameters;
    std::string instance_name = instance.first;

    if (instance.second->getMetaData().count("filename") > 0) {
      std::string debug_str = "Instance `" + instance_name + "` created at " +
        instance.second->getMetaData()["filename"].get<std::string>();
      if (instance.second->getMetaData().count("lineno") > 0) {
        debug_str += ":" +
          instance.second->getMetaData()["lineno"].get<std::string>();
      }
      body.push_back(std::make_unique<vAST::SingleLineComment>(debug_str));
    }

    std::unique_ptr<vAST::Connections>
      verilog_connections = std::make_unique<vAST::Connections>();
    RecordType* record_type = cast<RecordType>(instance_module->getType());
    for (auto field : record_type->getFields()) {
      Type* field_type = record_type->getRecord().at(field);
      if (!field_type->isInput()) {
        // output or inout, emit wire name
        verilog_connections->insert(
          field,
          std::make_unique<vAST::Identifier>(instance.first + "_" + field));
        continue;
      }
      auto entries = connection_map[ConnMapKey(instance.first, field)];
      if (entries.size() == 0) { continue; }
      else if (entries.size() > 1) {
        std::unique_ptr<vAST::Concat>
          concat = convert_non_bulk_connection_to_concat(
            field_type,
            entries,
            body,
            instance_name + "." + field,
            _inline);
        verilog_connections->insert(field, std::move(concat));
        // Otherwise we just use the entry in the connection map
      }
      else {
        std::unique_ptr<vAST::Expression> verilog_conn = convert_to_expression(
          convert_to_verilog_connection(entries[0].source, _inline));
        process_connection_debug_metadata(
          entries[0],
          verilog_conn->toString(),
          body,
          instance_name + "." + field);
        verilog_connections->insert(field, std::move(verilog_conn));
      }
    }
    bool is_mem_inst = instance_module->isGenerated() &&
      instance_module->getGenerator()->getName() == "mem" &&
      instance_module->getGenerator()->getNamespace()->getName() == "coreir";
    // Handle module arguments
    if (instance.second->hasModArgs()) {
      for (auto parameter : instance.second->getModArgs()) {
        std::unique_ptr<vAST::Expression> value;
        if (is_mem_inst && parameter.first == "init") {
          int width = dyn_cast<ConstInt>(
                        instance_module->getGenArgs().at("width"))
                        ->get();
          value = convert_mem_init_param_value(parameter.second, width);
        }
        else {
          value = convert_value(parameter.second);
        }
        instance_parameters.push_back(std::pair(
          std::make_unique<vAST::Identifier>(parameter.first),
          std::move(value)));
      }
    }
    // Handle generator arguments
    if (
      instance_module->isGenerated() &&
      instance_module->getGenerator()->getMetaData().count("verilog") > 0 &&
      // Ignore wrap "type" parameter
      instance_module->getGenerator()->getName() != "wrap") {
      for (auto parameter : instance.second->getModuleRef()->getGenArgs()) {
        instance_parameters.push_back(std::pair(
          std::make_unique<vAST::Identifier>(parameter.first),
          convert_value(parameter.second)));
      }
    }
    std::unique_ptr<vAST::StructuralStatement> statement;
    if (can_inline_binary_op(instance_module, _inline)) {
      statement = inline_binary_op(
        instance,
        std::move(verilog_connections),
        disable_width_cast);
    }
    else if (can_inline_unary_op(instance_module, _inline)) {
      bool is_wire = is_wire_module(instance_module);
      if (is_wire && !check_inline_verilog_wire_metadata(instance.second)) {
        wires.insert(instance.first);
      }
      statement = inline_unary_op(
        instance,
        std::move(verilog_connections),
        is_wire);
    }
    else if (can_inline_mux_op(instance_module, _inline)) {
      statement = inline_mux_op(instance, std::move(verilog_connections));
    }
    else if (can_inline_const_op(instance_module, _inline)) {
      ASSERT(
        instance_parameters[0].first->value == "value",
        "expected first param to be const value");
      statement = std::make_unique<vAST::ContinuousAssign>(
        std::make_unique<vAST::Identifier>(instance.first + "_out"),
        std::move(instance_parameters[0].second));
    }
    else if (can_inline_slice_op(instance_module, _inline)) {
      ASSERT(
        instance_parameters[0].first->value == "hi",
        "expected first param to be hi");
      ASSERT(
        instance_parameters[1].first->value == "lo",
        "expected second param to be lo");
      statement = std::make_unique<vAST::ContinuousAssign>(
        std::make_unique<vAST::Identifier>(instance.first + "_out"),
        std::make_unique<vAST::Slice>(
          verilog_connections->at("in"),
          vAST::make_binop(
            std::move(instance_parameters[0].second),
            vAST::BinOp::SUB,
            vAST::make_num("1")),
          std::move(instance_parameters[1].second)));
    }
    else if (instance_module->getMetaData().count("inline_verilog") > 0) {
      json metadata = instance_module->getMetaData();
      if (metadata.count("inline_verilog") > 0) {
        json inline_verilog = metadata["inline_verilog"];
        std::string inline_str = inline_verilog["str"].get<std::string>();
        for (auto it :
             json::iterator_wrapper(inline_verilog["connect_references"])) {
          SelectPath connect_select_path = splitString<SelectPath>(
            it.value().get<std::string>(),
            '.');
          ASSERT(connect_select_path[0] == "self", "Expected self reference");
          connect_select_path.pop_front();
          std::string value = verilog_connections
                                ->at(toString(connect_select_path))
                                ->toString();
          inline_str = std::regex_replace(
            inline_str,
            std::regex("\\{" + it.key() + "\\}"),
            value);
        }
        inline_verilog_body.push_back(
          std::make_unique<vAST::InlineVerilog>(inline_str));
      }
      // no statement to push
      continue;
    }
    else if (_inline && is_muxn(instance_module)) {
      int n = instance_module->getGenArgs().at("N")->get<int>();
      statement = make_muxn_if(std::move(verilog_connections), n);
    }
    else {
      statement = std::make_unique<vAST::ModuleInstantiation>(
        module_name,
        std::move(instance_parameters),
        instance_name,
        std::move(verilog_connections));
    }
    body.push_back(std::move(statement));
  }
  // Wire the outputs of the module and inout connections
  // TODO: Make these object methods so we don't have to pass things aorund so
  // much (e.g. _inline flag)
  assign_module_outputs(module_type, body, connection_map, _inline);
  assign_inouts(definition->getSortedConnections(), body, _inline);

  for (auto&& it : inline_verilog_body) { body.push_back(std::move(it)); }
  return body;
}  // namespace CoreIR

// Convert CoreIR paraemters into vAST Parameters
vAST::Parameters compile_params(Module* module) {
  vAST::Parameters parameters;
  std::set<std::string> parameters_seen;
  if (module->getModParams().size()) {
    for (auto parameter : module->getDefaultModArgs()) {
      parameters.push_back(std::pair(
        std::make_unique<vAST::Identifier>(parameter.first),
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
  return parameters;
}

void Passes::Verilog::compileModule(Module* module) {
  if (
    (module->getMetaData().count("inline_verilog") > 0) &&
    (module->getMetaData().count("verilog") > 0)) {
    LOG(WARN) << "WARNING: " + module->getRefName() +
        " has both `inline_verilog` and `verilog` metadata, `inline_verilog` "
        "will be ignored";
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    if (
      module->hasPrimitiveExpressionLambda() &&
      is_inlined(verilog_json["primitive_type"], module->getName()) &&
      this->_inline) {
      // Module is inlined
      return;
    }
    if (verilog_json.count("verilog_string") > 0) {
      // module is defined by a verilog string, we just emit the entire
      // string
      modules.push_back(
        std::make_pair(module->getName(), compile_string_module(verilog_json)));
    }
    else {
      std::string name = make_name(module->getName(), verilog_json);
      modules.push_back(std::make_pair(
        name,
        compileStringBodyModule(verilog_json, name, module)));
    }
    return;
  }
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    // This module is an instance of generator defined as a parametrized
    // verilog module
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    if (
      module->getGenerator()->hasPrimitiveExpressionLambda() &&
      is_inlined(verilog_json["primitive_type"], module->getName()) &&
      this->_inline) {
      // Module is inlined
      return;
    }
    std::string name = make_name(module->getName(), verilog_json);

    modules.push_back(std::make_pair(
      name,
      compileStringBodyModule(verilog_json, name, module)));

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
  if (module->getMetaData().count("inline_verilog") > 0) {
    // These are inlined directly into the module they are used
    return;
  }
  if (_inline && is_muxn(module)) {
    // Inlined into if statements
    return;
  }
  std::vector<std::unique_ptr<vAST::AbstractPort>> ports = compilePorts(
    cast<RecordType>(module->getType()));

  ModuleDef* definition = module->getDef();
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
    body;
  if (module->hasDef()) {
    body = compile_module_body(
      module->getType(),
      definition,
      this->_inline,
      this->disable_width_cast,
      this->wires);
  }

  if (module->getMetaData().count("filename") > 0) {
    std::string debug_str = "Module `" + module->getName() + "` defined at " +
      module->getMetaData()["filename"].get<std::string>();
    if (module->getMetaData().count("lineno") > 0) {
      debug_str += ":" + module->getMetaData()["lineno"].get<std::string>();
    }
    body.insert(
      body.begin(),
      std::make_unique<vAST::SingleLineComment>(debug_str));
  }

  vAST::Parameters parameters = compile_params(module);

  std::string name = module->getLongName();
  std::unique_ptr<vAST::AbstractModule>
    verilog_module = std::make_unique<vAST::Module>(
      name,
      std::move(ports),
      std::move(body),
      std::move(parameters));

  if (this->_inline) {
    vAST::AssignInliner assign_inliner(this->wires);
    verilog_module = assign_inliner.visit(std::move(verilog_module));
    AlwaysStarMerger always_star_merger;
    verilog_module = always_star_merger.visit(std::move(verilog_module));
  }
  modules.push_back(std::make_pair(name, std::move(verilog_module)));
}

bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* module = node.getModule();
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0 &&
    verilog_generators_seen.count(module->getGenerator()) > 0) {
    return false;
  }
  if (is_mantle_wire(module)) {
      // Check if all instances are inlined
      bool all_inlined = false;
      for (auto inst : node.getInstanceList()) {
          all_inlined = check_inline_verilog_wire_metadata(inst);
      }
      // if all inlined, don't compile the module
      if (all_inlined) return false;
  }
  compileModule(module);
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  for (auto& module : extern_modules) {
    os << vAST::SingleLineComment(
            "Module `" + module->getName() + "` defined externally")
            .toString()
       << std::endl;
  }
  for (auto& module : modules) { os << module.second->toString() << std::endl; }
}

void Passes::Verilog::writeToFiles(
  const std::string& dir,
  std::unique_ptr<std::string> product_file) {
  std::vector<std::string> products;
  for (auto& module : modules) {
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
  if (!product_file) return;
  std::ofstream fout(*product_file);
  ASSERT(fout.is_open(), "Cannot open file: " + *product_file);
  for (const auto& product : products) { fout << product << "\n"; }
  fout.close();
}

}  // namespace CoreIR
