#include "coreir/ir/coreir_symbol_table.hpp"

namespace CoreIR {

namespace {

using json_type = ::nlohmann::json;

template <typename Key, typename Value> struct Jsonifier {
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    return json_type(map);
  }
};

template <> struct Jsonifier<std::pair<std::string, std::string>, std::string> {
  using Key = std::pair<std::string, std::string>;
  using Value = std::string;
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::string> transformed;
    for (auto& [k, v] : map) {
      auto new_key = k.first + "," + k.second;
      transformed[new_key] = v;
    }
    return Jsonifier<std::string, std::string>()(transformed);
  }
};

}  // namespace

void CoreIRSymbolTable::setModuleName(
    std::string in_module_name, std::string out_module_name) {
  moduleNames.emplace(in_module_name, out_module_name);
}

void CoreIRSymbolTable::setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    std::string out_instance_name) {
  instanceNames.emplace(
      std::make_pair(in_module_name, in_instance_name), out_instance_name);
}

void CoreIRSymbolTable::setPortName(
    std::string in_module_name,
    std::string in_port_name,
    std::string out_port_name) {
  portNames.emplace(
      std::make_pair(in_module_name, in_port_name), out_port_name);
}

std::string CoreIRSymbolTable::getModuleName(std::string in_module_name) const {
  return moduleNames.at(in_module_name);
}

std::string CoreIRSymbolTable::getInstanceName(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceNames.at({in_module_name, in_instance_name});
}

std::string CoreIRSymbolTable::getPortName(
    std::string in_module_name, std::string in_port_name) const {
  return portNames.at({in_module_name, in_port_name});
}

json_type CoreIRSymbolTable::json() const {
  json_type ret;
  ret["module_names"] = Jsonifier<std::string, std::string>()(moduleNames);
  ret["instance_names"] = Jsonifier<StringPair, std::string>()(instanceNames);
  ret["port_names"] = Jsonifier<StringPair, std::string>()(portNames);
  return ret;
}

}  // namespace CoreIR
