#include "coreir/ir/coreir_symbol_table.hpp"

namespace CoreIR {

void CoreIRSymbolTable::setModuleName(
    std::string in_module_name, std::string out_module_name) {
}

void CoreIRSymbolTable::setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    std::string out_instance_name) {
}

void CoreIRSymbolTable::setPortName(
    std::string in_module_name,
    std::string in_port_name,
    std::string out_module_name,
    std::string out_port_name) {
}

std::string CoreIRSymbolTable::getModuleName(std::string in_module_name) const {
  return {};
}

std::string CoreIRSymbolTable::getInstanceName(
    std::string in_module_name, std::string in_instance_name) const {
  return {};
}

std::pair<std::string, std::string> CoreIRSymbolTable::getPortName(
    std::string in_module_name, std::string in_port_name) const {
  return {};
}

}  // namespace CoreIR
