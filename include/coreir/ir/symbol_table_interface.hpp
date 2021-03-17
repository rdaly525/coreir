#pragma once

#include <string>
#include <utility>
#include <variant>
#include "coreir/ir/json.h"

namespace CoreIR {

class SymbolTableSentinel {
 public:
  explicit SymbolTableSentinel(std::string flag) : flag(flag) {}
  ~SymbolTableSentinel() = default;

  const std::string& getFlag() const { return flag; }

 private:
  const std::string flag;
};

class SymbolTableInterface {
 public:
  using InstanceNameType = std::variant<
      SymbolTableSentinel const*, std::string>;

  virtual ~SymbolTableInterface() = default;

  virtual void setModuleName(
      std::string in_module_name, std::string out_module_name) = 0;
  virtual void setInstanceName(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_instance_name) = 0;
  virtual void setInstanceName(
      std::string in_module_name,
      std::string in_instance_name,
      SymbolTableSentinel* const out_instance_name) = 0;
  virtual void setPortName(
      std::string in_module_name,
      std::string in_port_name,
      std::string out_instance_name) = 0;
  virtual void setInlineInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name,
      std::string out_instance_name) = 0;
  virtual void setInlineInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name,
      SymbolTableSentinel* const out_instance_name) = 0;
  virtual void setInstanceType(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_type) = 0;

  virtual std::string getModuleName(std::string in_module_name) const = 0;
  virtual InstanceNameType getInstanceName(
      std::string in_module_name, std::string in_instance_name) const = 0;
  virtual std::string getPortName(
      std::string in_module_name, std::string in_port_name) const = 0;
  virtual InstanceNameType getInlinedInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name) const = 0;
  virtual std::string getInstanceType(
      std::string in_module_name,
      std::string in_instance_name) const = 0;

  virtual ::nlohmann::json json() const = 0;
};

}  // namespace CoreIR
