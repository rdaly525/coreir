#pragma once

#include <map>
#include <string>
#include "coreir/ir/symbol_table_interface.hpp"

namespace CoreIR {

class CoreIRSymbolTable : public SymbolTableInterface {
 public:
  CoreIRSymbolTable() = default;
  ~CoreIRSymbolTable() override = default;

  void setModuleName(
    std::string in_module_name, std::string out_module_name) override;
  void setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    std::string out_instance_name) override;
  void setPortName(
    std::string in_module_name,
    std::string in_port_name,
    std::string out_module_name,
    std::string out_port_name) override;

  std::string getModuleName(std::string in_module_name) const override;
  std::string getInstanceName(
    std::string in_module_name, std::string in_instance_name) const override;
  std::pair<std::string, std::string> getPortName(
    std::string in_module_name, std::string in_port_name) const override;

  ::nlohmann::json json() const override;

 private:
  using StringPair = std::pair<std::string, std::string>;

  std::map<std::string, std::string> moduleNames = {};
  std::map<StringPair, std::string> instanceNames = {};
  std::map<StringPair, StringPair> portNames = {};
};

}  // namespace CoreIR
