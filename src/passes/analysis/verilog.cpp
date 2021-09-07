#include "coreir/passes/analysis/verilog.h"
#include <fstream>
#include <regex>
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/passes/analysis/verilog/inline_utils.hpp"
#include "coreir/tools/cxxopts.h"
#include "verilogAST/assign_inliner.hpp"
#include "verilogAST/transformer.hpp"
#include "coreir/ir/symbol_table_interface.hpp"

namespace vAST = verilogAST;

template <typename... Ts>
std::string variant_to_string(std::variant<Ts...> &value) {
  return std::visit(
      [](auto &&value) -> std::string { return value->toString(); }, value);
}

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
    "Omit width cast in generated verilog when using inline")(
    "v,verilator-compat",
    "Emit primitives with verilator compatibility")(
    "p,prefix",
    "Prefix for emitted module names",
    cxxopts::value<std::string>())(
    "prefix-extern",
    "Use prefix (-p) for externally defined modules");
  auto opts = options.parse(argc, argv);
  if (opts.count("i")) { this->_inline = true; }
  if (opts.count("y")) { this->verilator_debug = true; }
  if (opts.count("w")) { this->disable_width_cast = true; }
  if (opts.count("v")) { this->verilator_compat = true; }
  if (opts.count("p")) {
    this->module_name_prefix = opts["p"].as<std::string>();
  }
  if (opts.count("prefix-extern")) { this->prefix_extern = true; }
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

  if (value->getKind() == Value::VK_Arg) {
    auto arg = dyn_cast<Arg>(value);
    return std::make_unique<vAST::Identifier>(arg->getField());
  }

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

void getNDArrayDims(Type* type, std::deque<int>& dims) {
  if (get_raw_type(type)->isBaseType()) { return; }
  else if (!isa<ArrayType>(type)) {
    throw std::runtime_error(
      "VERILOG BACKEND ERROR: Unsupported array type (not flattened or ndarray "
      "of bits)");
  }
  ArrayType* array_type = cast<ArrayType>(type);
  dims.push_back(array_type->getLen());
  getNDArrayDims(array_type->getElemType(), dims);
}

// Given a signal named `id` and a type `type`, wrap the signal name in a
// `Vector` node if the signal is of type Array
std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Vector>>
Passes::Verilog::processDecl(std::unique_ptr<vAST::Identifier> id, Type* type) {
  if (isa<ArrayType>(type)) {
    ArrayType* array_type = cast<ArrayType>(type);
    Type* internal_type = get_raw_type(array_type->getElemType());
    if (internal_type->isBaseType()) {
      return std::make_unique<vAST::Vector>(
        std::move(id),
        std::make_unique<vAST::NumericLiteral>(
          toString(array_type->getLen() - 1)),
        std::make_unique<vAST::NumericLiteral>("0"));
    }

    // Collect dimensions in a vector
    std::deque<int> dims;
    getNDArrayDims(type, dims);

    // Get outer dimension and remove from dims vector
    std::unique_ptr<vAST::NumericLiteral>
      inner_dim = std::make_unique<vAST::NumericLiteral>(
        toString(dims.back() - 1));
    dims.pop_back();

    // Convert to vAST
    std::vector<std::pair<
      std::unique_ptr<vAST::Expression>,
      std::unique_ptr<vAST::Expression>>>
      inner_dims;
    for (auto dim : dims) {
      inner_dims.push_back(
        {vAST::make_num(toString(dim - 1)), vAST::make_num("0")});
    }

    return std::make_unique<vAST::NDVector>(
      std::move(id),
      std::move(inner_dim),
      std::make_unique<vAST::NumericLiteral>("0"),
      std::move(inner_dims));
  }

  type = get_raw_type(type);
  ASSERT(type->isBaseType(), "Expected Bit, or Array of Bits");

  // If it's not an Array type, just return the original identifier
  return std::move(id);
}

void Passes::Verilog::makeDecl(
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
    this->processDecl(std::move(id), type));
}

// Make sure it doesn't conflict with any instance names
std::string genFreshWireName(
  std::string base_name,
  std::set<std::string>& instance_names) {
  if (!instance_names.count(base_name)) { return base_name; }
  int counter = 1;
  while (instance_names.count(base_name + "_unq" + std::to_string(counter))) {
    counter += 1;
  }
  return base_name + "_unq" + std::to_string(counter);
}

// Lookup to see if port name has been remapped (to avoid name conflicts with
// port and instance names)
std::string getUniquifiedName(
  std::map<std::string, std::string>& non_input_port_map,
  std::string port_name) {
  if (non_input_port_map.count(port_name)) {
    return non_input_port_map[port_name];
  }
  return port_name;
}

// Given a map of instances, return a vector of containing declarations for all
// the output ports of each instance.  We return a vector of a variant type for
// compatibility with the module AST node constructor, even though we only ever
// create Wire nodes.
std::vector<std::variant<
  std::unique_ptr<vAST::StructuralStatement>,
  std::unique_ptr<vAST::Declaration>>>
Passes::Verilog::declareConnections(
  std::map<std::string, Instance*> instances,
  bool _inline,
  std::set<std::string>& instance_names,
  std::map<std::string, std::string>& non_input_port_map) {
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
      this->makeDecl(instance.first, type, declarations, false);
      continue;
    }
    RecordType* record_type = cast<RecordType>(
      instance.second->getModuleRef()->getType());
    bool is_reg = _inline && is_muxn(instance.second->getModuleRef());
    for (auto field : record_type->getFields()) {
      Type* field_type = record_type->getRecord().at(field);
      if (field_type->isInput()) { continue; }
      std::string wire_name = instance.first + "_" + field;
      // Generate a fresh name in case theres a conflict with an existing
      // instance name
      wire_name = genFreshWireName(wire_name, instance_names);
      non_input_port_map[instance.first + "_" + field] = wire_name;
      // We don't need track conflicts with other instance port names this since
      // at this point the only identifiers introduced are inst_name + port
      // (and instance names must be unique), so only instance names can
      // clobber instance port names
      this->makeDecl(wire_name, field_type, declarations, is_reg);
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

// These memory modules have special handling for the verilog code generation
// of the `init` parameter in definitions
bool isVerilogMemPrimitive(Module* module) {
  return module->isGenerated() &&
    ((module->getGenerator()->getNamespace()->getName() == "coreir" &&
      module->getGenerator()->getName() == "mem") ||
     (module->getGenerator()->getNamespace()->getName() == "memory" &&
      module->getGenerator()->getName() == "sync_read_mem"));
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
    if (
      this->verilator_compat &&
      (name == "coreir_term" || name == "coreir_slice" ||
       name == "corebit_term")) {
      port_str = "/*verilator lint_off UNUSED */" + port_str +
        "/*verilator lint_on UNUSED */";
    }
    if (
      this->verilator_compat &&
      (name == "coreir_undriven" || name == "corebit_undriven")) {
      port_str = "/*verilator lint_off UNDRIVEN */" + port_str +
        "/*verilator lint_on UNDRIVEN */";
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
  // We always generate memory init param, even if has_init is false since the
  // verilog code expects it for syntax (just use a default value since the
  // generate if statement will not be run)
  if (isVerilogMemPrimitive(module)) {
    ASSERT(
      parameters_seen.count("init") == 0,
      "Did not expect to see init param already");
    parameters.push_back(std::pair(
      std::make_unique<vAST::Vector>(
        std::make_unique<vAST::Identifier>("init"),
        vAST::make_binop(
          vAST::make_binop(
            vAST::make_id("width"),
            vAST::BinOp::MUL,
            vAST::make_id("depth")),
          vAST::BinOp::SUB,
          vAST::make_num("1")),
        vAST::make_num("0")),
      std::make_unique<vAST::NumericLiteral>("0")));
  }
  for (auto parameter : module->getModParams()) {
    if (isVerilogMemPrimitive(module) && parameter.first == "init") {
      // Handled above, we always generate this parameter
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
      this->processDecl(std::move(name), field_type),
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
  std::vector<int> index;
  json& metadata;
  ConnMapEntry(Wireable* source, std::vector<int> index, json& metadata)
      : source(source),
        index(index),
        metadata(metadata){};
};

std::string indexToString(std::vector<int> index) {
  std::string str = "";
  for (auto i : index) { str += std::to_string(i) + ", "; }
  // remove extra comma/space
  str.resize(str.size() - 2);
  return str;
}

// Recursive logic for generating a Concat node for an ND Array connection
// if the array is 1 dimensional, just return a concat of the arguments
// else, build a concat for each index in the current outer most dimension
// (using recursion for each index in the dimension)
//
// Uses nd_args which contains the flat index space of connections and
// reconstructs the multi-dimensional concat tree
//
// offset argument is used to provide a start index for the final (leaf)
// recursion
std::unique_ptr<vAST::Concat> buildConcatFromNDArgs(
  std::vector<std::unique_ptr<vAST::Expression>>& nd_args,
  std::deque<int> dims,
  int offset = 0) {
  std::vector<std::unique_ptr<vAST::Expression>> args;
  int curr_dim = dims.front();
  if (dims.size() == 1) {
    // Simple case, concat args are fetched based on index from offset
    for (int i = 0; i < curr_dim; i++) {
      args.push_back(std::move(nd_args[offset + i]));
    }
  }
  else {
    std::deque<int> inner_dims = dims;
    inner_dims.pop_front();
    int inner_offset = 1;
    for (auto dim : inner_dims) { inner_offset *= dim; }
    // For each index in the current (outer) dimension
    // build concat for inner dimension(s) using offset that is incremented each
    // iteration
    for (int i = 0; i < curr_dim; i++) {
      args.push_back(
        buildConcatFromNDArgs(nd_args, inner_dims, offset + inner_offset * i));
    }
  }

  // Verilog uses MSB -> LSB ordering
  std::reverse(args.begin(), args.end());

  // Remove empty cells, since there might be slices that only populate the
  // start index of the slice
  args.erase(
    std::remove_if(
      args.begin(),
      args.end(),
      [](std::unique_ptr<vAST::Expression>& arg) {
        if (arg == NULL) { return true; }
        // Empty indices (e.g. connected by bulk or slice)
        if (auto ptr = dynamic_cast<vAST::Concat*>(arg.get())) {
          if (ptr->args.size() == 0) { return true; }
        }
        return false;
      }),
    args.end());

  // unpack concat of single element (handles bulk connections where only one
  // [the start] index is connected)
  // Right now this makes an assumption about how bulk connections are handled,
  // but it's hard to capture in an assertion
  for (unsigned int i = 0; i < args.size(); i++) {
    auto ptr = dynamic_cast<vAST::Concat*>(args[i].get());
    if (ptr && ptr->args.size() == 1) { args[i] = std::move(ptr->args[0]); }
  }
  bool unpacked = dims.size() != 1;
  return std::make_unique<vAST::Concat>(std::move(args), unpacked);
}

std::vector<int> selPathToIndex(SelectPath sp) {
  std::vector<int> index;
  for (unsigned int i = 2; i < sp.size(); i++) {
    index.push_back(std::stoi(sp[i]));
  }
  return index;
}

void addConnectionMapEntry(
  std::string inst_name,
  Wireable* sink,
  Wireable* source,
  std::map<ConnMapKey, std::vector<ConnMapEntry>>& connection_map,
  CoreIR::ModuleDef* definition) {
  SelectPath sink_sel_path = sink->getSelectPath();
  std::vector<int> index = selPathToIndex(sink_sel_path);
  connection_map[ConnMapKey(inst_name, sink_sel_path[1])].push_back(
    ConnMapEntry(source, index, definition->getMetaData(sink, source)));
}

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
  std::map<std::string, Instance*> instances,
  std::vector<Connection>& connections) {
  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map;
  for (auto connection : connections) {
    if (connection.first->getType()->isInput()) {
      addConnectionMapEntry(
        connection.first->getSelectPath()[0],
        connection.first,
        connection.second,
        connection_map,
        definition);
    }
    else if (connection.second->getType()->isInput()) {
      addConnectionMapEntry(
        connection.second->getSelectPath()[0],
        connection.second,
        connection.first,
        connection_map,
        definition);
    }
  }
  return connection_map;
}  // namespace CoreIR

// Join select path fields by "_" (ignoring intial self if present)
std::variant<
  std::unique_ptr<vAST::Identifier>,
  std::unique_ptr<vAST::Attribute>,
  std::unique_ptr<vAST::Index>,
  std::unique_ptr<vAST::Slice>>
convert_to_verilog_connection(
  Wireable* value,
  bool _inline,
  std::map<std::string, std::string>& non_input_port_map) {
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
  Wireable* curr_wireable = parent;

  std::variant<
    std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::Attribute>,
    std::unique_ptr<vAST::Slice>,
    std::unique_ptr<vAST::Index>>
    curr_node;
  for (uint i = 0; i < select_path.size(); i++) {
    auto item = select_path[i];
    if (isNumber(item)) {
      if (std::holds_alternative<std::unique_ptr<vAST::Identifier>>(
            curr_node)) {
        std::unique_ptr<vAST::Identifier>
          id = std::get<std::unique_ptr<vAST::Identifier>>(
            std::move(curr_node));
        id->value = getUniquifiedName(non_input_port_map, id->value);
        curr_node = std::move(id);
      }
      curr_node = std::make_unique<vAST::Index>(
        std::move(curr_node),
        vAST::make_num(item));
    }
    else if (isSlice(item)) {
      if (std::holds_alternative<std::unique_ptr<vAST::Identifier>>(
            curr_node)) {
        std::unique_ptr<vAST::Identifier>
          id = std::get<std::unique_ptr<vAST::Identifier>>(
            std::move(curr_node));
        id->value = getUniquifiedName(non_input_port_map, id->value);
        curr_node = std::move(id);
      }
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
            getUniquifiedName(non_input_port_map, item));
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
  if (std::holds_alternative<std::unique_ptr<vAST::Index>>(curr_node)) {
    return std::get<std::unique_ptr<vAST::Index>>(std::move(curr_node));
  }
  if (std::holds_alternative<std::unique_ptr<vAST::Identifier>>(curr_node)) {
    std::unique_ptr<vAST::Identifier>
      id = std::get<std::unique_ptr<vAST::Identifier>>(std::move(curr_node));
    id->value = getUniquifiedName(non_input_port_map, id->value);
    return std::move(id);
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
  bool _inline,
  std::map<std::string, std::string>& non_input_port_map) {

  // nd-args contains a flat encoding of the index space of the array
  std::vector<std::unique_ptr<vAST::Expression>> nd_args;
  ASSERT(isa<ArrayType>(field_type), "Expected Array for concat connection");
  ArrayType* arr_type = cast<ArrayType>(field_type);

  std::deque<int> dims;
  getNDArrayDims(arr_type, dims);
  int total_size = 1;
  for (auto dim : dims) { total_size *= dim; }
  nd_args.resize(total_size);

  // map entries from the connection map into the flat index space, then we
  // construct the appropriate Concat tree to map to the multi-dimensional space
  for (auto entry : entries) {
    std::unique_ptr<vAST::Expression> verilog_conn = convert_to_expression(
      convert_to_verilog_connection(entry.source, _inline, non_input_port_map));
    process_connection_debug_metadata(
      entry,
      verilog_conn->toString(),
      body,
      debug_prefix + "[" + indexToString(entry.index) + "]");
    ASSERT(
      entry.index.size() <= dims.size(),
      "Expected index size to be less than or equal to dimensions");
    // convert index vector to flat index
    int inner_offset = total_size;
    int index = 0;
    for (unsigned int i = 0; i < entry.index.size(); i++) {
      inner_offset /= dims[i];
      if (i < dims.size() - 1) { index += entry.index[i] * inner_offset; }
      else {
        index += entry.index[i];
      }
    }
    nd_args[index] = std::move(verilog_conn);
  }

  return buildConcatFromNDArgs(nd_args, dims);
}

std::variant<
  std::unique_ptr<vAST::Identifier>,
  std::unique_ptr<vAST::Index>,
  std::unique_ptr<vAST::Slice>>
processSingleArrayElementTarget(
  std::string target_id,
  Type* type,
  std::vector<ConnMapEntry>& entries) {
  std::variant<std::unique_ptr<vAST::Identifier>, std::unique_ptr<vAST::Index>>
    target = std::make_unique<vAST::Identifier>(target_id);
  // handle single entry for array of length 1
  // e.g. assign x[0] = y;
  // Check if array is length 1, because sometimes we only have one connection
  // for a slice
  //
  // Also for bit <- bits[1] in verilog, we don't don't need to do this (but
  // we do need to for unpacked multidimensional arrays)
  while (isa<ArrayType>(type) && cast<ArrayType>(type)->getLen() == 1 &&
         !get_raw_type(cast<ArrayType>(type)->getElemType())->isBaseType() &&
         (entries.size() == 1) && (entries[0].index.size() > 0)) {
    target = std::make_unique<vAST::Index>(
      std::visit(
        [](auto&& target) -> std::variant<
                            std::unique_ptr<vAST::Identifier>,
                            std::unique_ptr<vAST::Attribute>,
                            std::unique_ptr<vAST::Slice>,
                            std::unique_ptr<vAST::Index>> {
          return std::move(target);
        },
        std::move(target)),
      vAST::make_num("0"));
    type = cast<ArrayType>(type)->getElemType();
  }
  return std::visit(
    [](auto&& arg) -> std::variant<
                     std::unique_ptr<vAST::Identifier>,
                     std::unique_ptr<vAST::Index>,
                     std::unique_ptr<vAST::Slice>> { return std::move(arg); },
    std::move(target));
}

// unpacked concat doesn't seem to work with ncsim/garnet test,
// so instead we emit an assignment statement for each index of the
// unpacked array
void wireUnpackedDriver(
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  std::unique_ptr<vAST::Concat> concat,
  std::variant<
    std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::Index>,
    std::unique_ptr<vAST::Slice>> target) {
  unsigned int len = concat->args.size();
  for (unsigned int i = 0; i < len; i++) {
    std::unique_ptr<vAST::Expression> curr_arg = std::move(concat->args[i]);
    std::variant<
      std::unique_ptr<vAST::Identifier>,
      std::unique_ptr<vAST::Index>,
      std::unique_ptr<vAST::Slice>>
      curr_target = std::make_unique<vAST::Index>(
        std::visit(
          [](auto&& value) -> std::variant<
                             std::unique_ptr<vAST::Identifier>,
                             std::unique_ptr<vAST::Attribute>,
                             std::unique_ptr<vAST::Slice>,
                             std::unique_ptr<vAST::Index>> {
            return value->clone();
          },
          target),
        vAST::make_num(std::to_string(len - 1 - i)));
    if (auto ptr = dynamic_cast<vAST::Concat*>(curr_arg.get())) {
      if (ptr->unpacked) {
        curr_arg.release();
        wireUnpackedDriver(
          body,
          std::unique_ptr<vAST::Concat>(ptr),
          std::move(curr_target));
        continue;
      }
    }
    body.push_back(std::make_unique<vAST::ContinuousAssign>(
      std::move(curr_target),
      std::move(curr_arg)));
  }
}

// For each output of the current module definition, emit a statement of the
// form: `assign <output> = <driver(s)>;`
void assign_module_outputs(
  RecordType* record_type,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  std::map<ConnMapKey, std::vector<ConnMapEntry>> connection_map,
  bool _inline,
  std::map<std::string, std::string>& non_input_port_map) {
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
          _inline,
          non_input_port_map);
      if (concat->unpacked) {
        wireUnpackedDriver(body, std::move(concat), vAST::make_id(field));
      }
      else {
        body.push_back(std::make_unique<vAST::ContinuousAssign>(
          std::make_unique<vAST::Identifier>(field),
          std::move(concat)));
      }
    }
    else {
      std::unique_ptr<vAST::Expression> verilog_conn = convert_to_expression(
        convert_to_verilog_connection(
          entries[0].source,
          _inline,
          non_input_port_map));
      process_connection_debug_metadata(
        entries[0],
        verilog_conn->toString(),
        body,
        field);

      std::variant<
        std::unique_ptr<vAST::Identifier>,
        std::unique_ptr<vAST::Index>,
        std::unique_ptr<vAST::Slice>>
        target = processSingleArrayElementTarget(field, field_type, entries);

      // Regular (possibly bulk) connection
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
        std::move(target),
        std::move(verilog_conn)));
    }
  }
}

// assign inout ports
void assign_inouts(
  std::vector<Connection>& connections,
  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>& body,
  bool _inline,
  std::map<std::string, std::string>& non_input_port_map) {
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
      // logic depends on the input/output relationship (output drives input)
      // so the order is enforced through other means
      Wireable* target = connection.first;
      Wireable* value = connection.second;
      bool order = SPComp(target->getSelectPath(), value->getSelectPath());
      if (!order) { std::swap(target, value); }
      body.push_back(std::make_unique<vAST::ContinuousAssign>(
        convert_to_assign_target(
          convert_to_verilog_connection(target, _inline, non_input_port_map)),
        convert_to_expression(
          convert_to_verilog_connection(value, _inline, non_input_port_map))));
    };
  };
}

// These memory modules have special handling for the `init` parameter in
// verilog code generation of instances
bool isMemModule(Module* module) {
  return module->isGenerated() &&
    ((module->getGenerator()->getNamespace()->getName() == "coreir" &&
      (module->getGenerator()->getName() == "mem")) ||
     (module->getGenerator()->getNamespace()->getName() == "memory" &&
      (module->getGenerator()->getName() == "rom2" ||
       module->getGenerator()->getName() == "sync_read_mem")));
}

// Traverses the instance map and creates a vector of module instantiations
// using connection_map to wire up instance ports
std::vector<std::variant<
  std::unique_ptr<vAST::StructuralStatement>,
  std::unique_ptr<vAST::Declaration>>>
Passes::Verilog::compileModuleBody(
  RecordType* module_type,
  CoreIR::ModuleDef* definition,
  bool _inline,
  bool disable_width_cast,
  std::set<std::string>& wires,
  std::set<std::string>& inlined_wires) {

  std::set<std::string> instance_names;
  std::map<std::string, std::string> non_input_port_map;

  std::map<std::string, Instance*> instances = definition->getInstances();

  // initialize used ids with instance names
  std::transform(
    instances.begin(),
    instances.end(),
    std::inserter(instance_names, instance_names.end()),
    [](auto pair) { return pair.first; });

  std::vector<std::unique_ptr<vAST::StructuralStatement>> inline_verilog_body;

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
    body = this->declareConnections(
      instances,
      _inline,
      instance_names,
      non_input_port_map);

  std::vector<Connection> connections = definition->getSortedConnections();

  std::map<ConnMapKey, std::vector<ConnMapEntry>>
    connection_map = build_connection_map(definition, instances, connections);

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
      // Allow user to provide specific module verilog name using metadata
      // (e.g. for ice40 primitives that are normally contained in the ice40
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
      std::string wire_name = instance.first + "_" + field;
      if (!field_type->isInput()) {
        // connect wire
        verilog_connections->insert(
          field,
          std::make_unique<vAST::Identifier>(
            getUniquifiedName(non_input_port_map, wire_name)));
        continue;
      }

      bool is_inlined = isInlined(instance_module, _inline);
      auto entries = connection_map[ConnMapKey(instance.first, field)];
      std::unique_ptr<vAST::Expression> driver;
      if (entries.size() == 0) {
        throw std::runtime_error(
          "COREIR_VERILOG_ERROR: No connections driving input");
      }
      else if (entries.size() > 1) {
        std::unique_ptr<vAST::Concat>
          concat = convert_non_bulk_connection_to_concat(
            field_type,
            entries,
            body,
            instance_name + "." + field,
            _inline,
            non_input_port_map);
        if (concat->unpacked && !is_inlined) {
          wire_name = genFreshWireName(wire_name, instance_names);
          this->makeDecl(wire_name, field_type, body, false);
          wires.insert(wire_name);
          verilog_connections->insert(
            field,
            std::make_unique<vAST::Identifier>(wire_name));
          wireUnpackedDriver(body, std::move(concat), vAST::make_id(wire_name));
          continue;
        }
        driver = std::move(concat);
      }
      else {
        driver = convert_to_expression(convert_to_verilog_connection(
          entries[0].source,
          _inline,
          non_input_port_map));
        process_connection_debug_metadata(
          entries[0],
          driver->toString(),
          body,
          instance_name + "." + field);
      }
      if (is_inlined) {
        // insert into connections since it will be extracted by inline logic
        // (don't need input wire assign)
        verilog_connections->insert(field, std::move(driver));
      }
      else {
        std::variant<
          std::unique_ptr<vAST::Identifier>,
          std::unique_ptr<vAST::Index>,
          std::unique_ptr<vAST::Slice>>
          target = processSingleArrayElementTarget(
            wire_name,
            field_type,
            entries);
        auto driver_id = dynamic_cast<vAST::Identifier*>(driver.get());
        auto driver_index = dynamic_cast<vAST::Index*>(driver.get());
        auto driver_slice = dynamic_cast<vAST::Slice*>(driver.get());
        if (
          (driver_id || driver_index || driver_slice) &&
          std::holds_alternative<std::unique_ptr<vAST::Identifier>>(target)) {
          // If it's not a concat, we connect it directly
          verilog_connections->insert(field, std::move(driver));
        }
        else {
          // otherwise it's a concat, so we emit an input wire for it
          wire_name = genFreshWireName(wire_name, instance_names);
          this->makeDecl(wire_name, field_type, body, false);
          verilog_connections->insert(
            field,
            std::make_unique<vAST::Identifier>(wire_name));

          // Regular (possibly bulk) connection
          body.push_back(std::make_unique<vAST::ContinuousAssign>(
            std::move(target),
            std::move(driver)));
        }
      }
    }
    bool is_mem_inst = isMemModule(instance_module);
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
      if (is_wire) { wires.insert(instance.first); }
      if (check_inline_verilog_wire_metadata(instance.second)) {
        // We handle these later since instance inputs will mark wire inputs to
        // prevent inlining, but we override that with this metadata after
        // instance inputs have been processed
        inlined_wires.insert(instance.first);
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
        std::get<std::unique_ptr<vAST::Identifier>>(
          instance_parameters[0].first)
            ->value == "value",
        "expected first param to be const value");
      statement = std::make_unique<vAST::ContinuousAssign>(
        std::make_unique<vAST::Identifier>(instance.first + "_out"),
        std::move(instance_parameters[0].second));
    }
    else if (can_inline_slice_op(instance_module, _inline)) {
      ASSERT(
        std::get<std::unique_ptr<vAST::Identifier>>(
          instance_parameters[0].first)
            ->value == "hi",
        "expected first param to be hi");
      ASSERT(
        std::get<std::unique_ptr<vAST::Identifier>>(
          instance_parameters[1].first)
            ->value == "lo",
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
             inline_verilog["connect_references"].items()) {
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
      auto metadata = instance.second->getMetaData();
      if (metadata.count("compile_guard") > 0) {
        std::vector<std::variant<
          std::unique_ptr<vAST::StructuralStatement>,
          std::unique_ptr<vAST::Declaration>>>
          true_body;
        true_body.push_back(std::move(statement));
        std::string type = metadata["compile_guard"]["type"];

        std::vector<std::variant<
          std::unique_ptr<vAST::StructuralStatement>,
          std::unique_ptr<vAST::Declaration>>>
          else_body;
        RecordType* record_type = cast<RecordType>(instance_module->getType());
        for (auto field : record_type->getFields()) {
          Type* field_type = record_type->getRecord().at(field);
          std::string wire_name = instance.first + "_" + field;
          if (!field_type->isInput()) {
            else_body.push_back(std::make_unique<vAST::ContinuousAssign>(
              std::make_unique<vAST::Identifier>(
                getUniquifiedName(non_input_port_map, wire_name)),
              vAST::make_num("0")));
          }
        }

        if (type == "defined") {
          statement = std::make_unique<vAST::IfDef>(
            metadata["compile_guard"]["condition_str"].get<std::string>(),
            std::move(true_body),
            std::move(else_body));
        }
        else if (type == "undefined") {
          statement = std::make_unique<vAST::IfNDef>(
            metadata["compile_guard"]["condition_str"].get<std::string>(),
            std::move(true_body),
            std::move(else_body));
        }
        else {
          throw std::runtime_error("Unexpected compile_guard type: " + type);
        }
      }
      // TODO(rsetaluri): We should really log an instance "rename" here for
      // maintaining the symbol table.
    }
    body.push_back(std::move(statement));
  }
  // Wire the outputs of the module and inout connections
  // TODO: Make these object methods so we don't have to pass things aorund so
  // much (e.g. _inline flag)
  assign_module_outputs(
    module_type,
    body,
    connection_map,
    _inline,
    non_input_port_map);
  assign_inouts(connections, body, _inline, non_input_port_map);

  for (auto&& it : inline_verilog_body) { body.push_back(std::move(it)); }
  return body;
}  // namespace CoreIR

std::vector<std::variant<
  std::unique_ptr<vAST::StructuralStatement>,
  std::unique_ptr<vAST::Declaration>>>
Passes::Verilog::compileLinkedModuleBody(Module* module) {

  std::vector<std::variant<
    std::unique_ptr<vAST::StructuralStatement>,
    std::unique_ptr<vAST::Declaration>>>
    body;

  auto linkedModules = module->getLinkedModules();
  auto linkedModulesIter = linkedModules.begin();

  // Default definition is either default linked module or one and only entry
  // in linked modules map
  std::string default_mod_str;
  if (module->hasDefaultLinkedModule()) {
    default_mod_str = this->linked_module_map[module->getDefaultLinkedModule()];
  }
  else if (linkedModules.size() == 1) {
    default_mod_str = this->linked_module_map[linkedModulesIter->second];
    linkedModulesIter = ++linkedModulesIter;
  }

  if (default_mod_str != "") {
    body.push_back(
      std::make_unique<vAST::InlineVerilog>(default_mod_str));
  }

  if (linkedModules.size() > 0) {
    while (linkedModulesIter != linkedModules.end()) {
      auto entry = *linkedModulesIter;
      std::string linked_module_str = linked_module_map[entry.second];
      std::vector<std::variant<
        std::unique_ptr<vAST::StructuralStatement>,
        std::unique_ptr<vAST::Declaration>>>
        true_body;
      true_body.push_back(
        std::make_unique<vAST::InlineVerilog>(linked_module_str));
      auto node = std::make_unique<vAST::IfDef>(
        entry.first,
        std::move(true_body),
        std::move(body));
      std::vector<std::variant<
        std::unique_ptr<vAST::StructuralStatement>,
        std::unique_ptr<vAST::Declaration>>>
        new_body;
      new_body.push_back(std::move(node));
      body = std::move(new_body);
      linkedModulesIter = ++linkedModulesIter;
    }
  }
  return body;
}

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
    else if (verilog_json.count("verilog_body") > 0) {
      std::vector<std::unique_ptr<vAST::AbstractPort>> ports = compilePorts(
        cast<RecordType>(module->getType()));

      std::vector<std::variant<
        std::unique_ptr<vAST::StructuralStatement>,
        std::unique_ptr<vAST::Declaration>>>
        body;

      body.push_back(std::make_unique<vAST::InlineVerilog>(
        verilog_json["verilog_body"].get<std::string>()));

      std::string name = module->getLongName();
      modules.push_back(std::make_pair(
        name,
        std::make_unique<vAST::Module>(
          name,
          std::move(ports),
          std::move(body))));
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
  if (!(module->hasDef() || module->hasVerilogDef() ||
        module->hasLinkedModule())) {
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

  // Keep track of wire primitive instances, we do not inline these
  std::set<std::string> wires;

  // Wires marked to force inlining (overrides standard wire inline blocking
  // logic)
  std::set<std::string> inlined_wires;

  if (module->hasDef()) {
    body = this->compileModuleBody(
      module->getType(),
      definition,
      this->_inline,
      this->disable_width_cast,
      wires,
      inlined_wires);
  }

  if (module->hasLinkedModule()) {
    body = this->compileLinkedModuleBody(module);
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
  // NOTE(rsetaluri): This is an example of updating an entry in the symbol
  // table.
  this->getSymbolTable()->setModuleName(module->getLongName(), name);
  std::unique_ptr<vAST::Module>
    verilog_module = std::make_unique<vAST::Module>(
      name,
      std::move(ports),
      std::move(body),
      std::move(parameters));

  if (this->_inline) {
    for (auto wire : inlined_wires) {
      // force inlining of wires based on metadata
      wires.erase(wire);
    }
    vAST::AssignInliner assign_inliner(wires);
    verilog_module = assign_inliner.visit(std::move(verilog_module));
    AlwaysStarMerger always_star_merger;
    verilog_module = always_star_merger.visit(std::move(verilog_module));
  }
  std::string module_str;
  for (auto& statement : verilog_module->body) {
    module_str += variant_to_string(statement) + "\n";
  }
  linked_module_map[module] = module_str;
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
  if (this->_inline && is_mantle_wire(module)) {
    // Mantle wire modules are always inlined into verilog wires rather than
    // module instances (but not all the verilog wires are inlined, based on
    // metadata)
    return false;
  }
  compileModule(module);
  return false;
}

class InstancePrefixInserter : public vAST::Transformer {
  std::set<std::string> renamed_modules;
  std::string prefix;

 public:
  InstancePrefixInserter(
    std::set<std::string> renamed_modules,
    std::string prefix)
      : renamed_modules(renamed_modules),
        prefix(prefix){};

  using vAST::Transformer::visit;
  virtual std::unique_ptr<vAST::ModuleInstantiation> visit(
    std::unique_ptr<vAST::ModuleInstantiation> node) {
    if (renamed_modules.count(node->module_name)) {
      node->module_name = prefix + node->module_name;
    }
    return node;
  }
};

void Passes::Verilog::addPrefix() {
  if (this->prefixAdded || this->module_name_prefix == "") return;

  // TODO(rsetaluri,rdaly525,leonardt): Instrument symbol table updates for this
  // routine.

  std::set<std::string> renamed_modules;
  for (auto& module : this->modules) {
    // Note we cannot add prefix to string modules since their
    // module name is inside an opaque verilog string
    if (auto ptr = dynamic_cast<vAST::Module*>(module.second.get())) {
      ptr->name = this->module_name_prefix + ptr->name;
      renamed_modules.insert(module.first);
    }
  }

  if (this->prefix_extern) {
    for (auto& module : extern_modules) {
      if (module->getMetaData().count("verilog_name") > 0) {
        // Overridden (e.g. for ice40 modules, we don't want the namespace
        // prefix)
        continue;
      }
      renamed_modules.insert(module->getLongName());
    }
  }

  InstancePrefixInserter transformer(renamed_modules, module_name_prefix);
  for (auto& module : modules) {
    module.second = transformer.visit(std::move(module.second));
  }

  this->prefixAdded = true;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  this->addPrefix();
  for (auto& module : extern_modules) {
    // We do prefix logic here rather than modify the coreir name in the
    // addPrefix logic (since this verilog contained and there's no verilog to
    // modify for this).
    std::string name;
    if (module->getMetaData().count("verilog_name") > 0) {
      // Overridden (e.g. for ice40 modules, where a prefix shouldn't be used)
      name = module->getMetaData()["verilog_name"].get<std::string>();
    }
    else {
      name = module->getLongName();
      if (this->prefix_extern) name = this->module_name_prefix + name;
    }
    const auto comment = "Module `" + name + "` defined externally";
    os << vAST::SingleLineComment(comment).toString() << std::endl;
  }
  for (auto& module : modules) {
    os << module.second->toString() << std::endl;
  }
}

void Passes::Verilog::writeToFiles(
  const std::string& dir,
  std::unique_ptr<std::string> product_file,
  std::string outExt) {
  std::vector<std::string> products;
  ASSERT(
    outExt == "v" || outExt == "sv",
    "Expect outext to be v or sv, not " + outExt);
  this->addPrefix();
  for (auto& module : modules) {
    const std::string filename = module.first + "." + outExt;
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
