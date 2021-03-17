#include "coreir/ir/coreir_symbol_table.hpp"

namespace CoreIR {

namespace {

using json_type = ::nlohmann::json;
using InstanceNameType = SymbolTableInterface::InstanceNameType;
using StringPair = std::array<std::string, 2>;
using InlinedInstanceKey = std::pair<std::string, std::vector<std::string>>;

template <typename Key, typename Value> struct Jsonifier {
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    return json_type(map);
  }
};

template <typename CollectionType> std::string joinStrings(
    const CollectionType& collection, std::string seperator = ",") {
  if (collection.size() == 0) return "";
  auto joined = collection[0];
  const auto bound = static_cast<int>(collection.size());
  for (int i = 1; i < bound; i++) {
    joined += (seperator + collection[i]);
  }
  return joined;
}

template <std::size_t N>
struct Jsonifier<std::array<std::string, N>, std::string> {
  using Key = std::array<std::string, N>;
  using Value = std::string;
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::string> transformed;
    for (auto& [k, v] : map) {
      auto new_key = joinStrings(k);
      transformed[new_key] = v;
    }
    return Jsonifier<std::string, std::string>()(transformed);
  }
};

template <std::size_t N>
struct Jsonifier<std::array<std::string, N>, InstanceNameType> {
  using Key = std::array<std::string, N>;
  using Value = InstanceNameType;
  using map_type = std::map<Key, Value>;

  struct ValueStringifier {
    std::string operator()(const CoreIR::SymbolTableSentinel *const & s) const {
      return s->getFlag();
    }
    std::string operator()(const std::string& s) const { return s; }
  };

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::string> transformed;
    for (auto& [k, v] : map) {
      auto new_key = joinStrings(k);
      auto new_value = std::visit(ValueStringifier{}, v);
      transformed[new_key] = new_value;
    }
    return Jsonifier<std::string, std::string>()(transformed);
  }
};

template <> struct Jsonifier<InlinedInstanceKey, InstanceNameType> {
  using Key = InlinedInstanceKey;
  using Value = InstanceNameType;
  using map_type = std::map<Key, Value>;

  struct ValueStringifier {
    std::string operator()(const CoreIR::SymbolTableSentinel *const & s) const {
      return s->getFlag();
    }
    std::string operator()(const std::string& s) const { return s; }
  };

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::string> transformed;
    for (auto& [k, v] : map) {
      auto new_key = joinStrings(std::vector{k.first, joinStrings(k.second)});
      auto new_value = std::visit(ValueStringifier{}, v);
      transformed[new_key] = new_value;
    }
    return Jsonifier<std::string, std::string>()(transformed);
  }
};

}  // namespace

SymbolTableSentinel* const symbolTableInlinedInstanceSentinel() {
  static SymbolTableSentinel sentinel("__SYMBOL_TABLE_INLINED_INSTANCE__");
  return &sentinel;
}

void CoreIRSymbolTable::setModuleName(
    std::string in_module_name, std::string out_module_name) {
  moduleNames.emplace(in_module_name, out_module_name);
}

void CoreIRSymbolTable::setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    std::string out_instance_name) {
  std::array key = {in_module_name, in_instance_name};
  instanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    SymbolTableSentinel* const out_instance_name) {
  std::array key = {in_module_name, in_instance_name};
  instanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setPortName(
    std::string in_module_name,
    std::string in_port_name,
    std::string out_port_name) {
  std::array key = {in_module_name, in_port_name};
  portNames.emplace(key, out_port_name);
}

void CoreIRSymbolTable::setInlineInstanceName(
      std::string in_module_name,
      std::vector<std::string> in_instance_names,
      std::string out_instance_name) {
  const auto key = std::make_pair(in_module_name, in_instance_names);
  inlinedInstanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setInlineInstanceName(
      std::string in_module_name,
      std::vector<std::string> in_instance_names,
      SymbolTableSentinel* const out_instance_name) {
  const auto key = std::make_pair(in_module_name, in_instance_names);
  inlinedInstanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setInstanceType(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_type) {
  std::array key = {in_module_name, in_instance_name};
  instanceTypes.emplace(key, out_type);
}

std::string CoreIRSymbolTable::getModuleName(std::string in_module_name) const {
  return moduleNames.at(in_module_name);
}

InstanceNameType CoreIRSymbolTable::getInstanceName(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceNames.at({in_module_name, in_instance_name});
}

std::string CoreIRSymbolTable::getPortName(
    std::string in_module_name, std::string in_port_name) const {
  return portNames.at({in_module_name, in_port_name});
}

InstanceNameType CoreIRSymbolTable::getInlinedInstanceName(
    std::string in_module_name,
    std::vector<std::string> in_instance_names) const {
  return inlinedInstanceNames.at({in_module_name, in_instance_names});
}

std::string CoreIRSymbolTable::getInstanceType(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceTypes.at({in_module_name, in_instance_name});
}

json_type CoreIRSymbolTable::json() const {
  using InlinedInstanceJsonifier = Jsonifier<InlinedInstanceKey,
                                             InstanceNameType>;
  json_type ret;
  ret["module_names"] = Jsonifier<std::string, std::string>()(moduleNames);
  ret["instance_names"] = Jsonifier<StringPair, InstanceNameType>()(
      instanceNames);
  ret["port_names"] = Jsonifier<StringPair, std::string>()(portNames);
  ret["inlined_instance_names"] = InlinedInstanceJsonifier()(
      inlinedInstanceNames);
  ret["instance_types"] = Jsonifier<StringPair, std::string>()(instanceTypes);
  return ret;
}

}  // namespace CoreIR
