#pragma once

#include <array>
#include <map>
#include <string>
#include "coreir/ir/symbol_table_interface.hpp"

namespace CoreIR {

SymbolTableSentinel* const symbolTableInlinedInstanceSentinel();
SymbolTableSentinel* const symbolTableEmptySentinel();

class CoreIRSymbolTable : public SymbolTableInterface {
 public:
  CoreIRSymbolTable();
  ~CoreIRSymbolTable() override = default;

  void setModuleName(
      std::string in_module_name, std::string out_module_name) override;
  void setInstanceName(
      std::string in_module_name,
      std::string in_instance_name,
      InstanceNameType out_instance_name) override;
  void setPortName(
      std::string in_module_name,
      std::string in_port_name,
      std::string out_port_name) override;
  void setInlinedInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name,
      InstanceNameType out_instance_name) override;
  void setInstanceType(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_type) override;

  std::string getModuleName(std::string in_module_name) const override;
  InstanceNameType getInstanceName(
      std::string in_module_name, std::string in_instance_name) const override;
  std::string getPortName(
      std::string in_module_name, std::string in_port_name) const override;
  InstanceNameType getInlinedInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name) const override;
  std::string getInstanceType(
      std::string in_module_name,
      std::string in_instance_name) const override;

  SymbolTableLoggerInterface* getLogger() override { return logger.get(); }
  bool finalizeLogger() override { return logger->finalize(); }

  ::nlohmann::json json() const override;

 private:
  using StringPair = std::array<std::string, 2>;
  using StringTriple = std::array<std::string, 3>;

  std::map<std::string, std::string> moduleNames = {};
  std::map<StringPair, InstanceNameType> instanceNames = {};
  std::map<StringPair, std::string> portNames = {};
  std::map<StringTriple, InstanceNameType> inlinedInstanceNames = {};
  std::map<StringPair, std::string> instanceTypes = {};

  std::unique_ptr<SymbolTableLoggerInterface> logger;
};

}  // namespace CoreIR
