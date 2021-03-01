#include "coreir/ir/coreir_symbol_table.hpp"

namespace CoreIR {

namespace {

using json = ::nlohmann::json;

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
    std::string out_module_name,
    std::string out_port_name) {
  portNames.emplace(
      std::make_pair(in_module_name, in_port_name),
      std::make_pair(out_module_name, out_port_name));
}

std::string CoreIRSymbolTable::getModuleName(std::string in_module_name) const {
  return moduleNames.at(in_module_name);
}

std::string CoreIRSymbolTable::getInstanceName(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceNames.at({in_module_name, in_instance_name});
}

std::pair<std::string, std::string> CoreIRSymbolTable::getPortName(
    std::string in_module_name, std::string in_port_name) const {
  return portNames.at({in_module_name, in_port_name});
}

json CoreIRSymbolTable::json() const {
  return {};
}

}  // namespace CoreIR
