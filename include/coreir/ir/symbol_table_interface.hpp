#pragma once

#include <string>
#include <utility>
#include "coreir/ir/json.h"

namespace CoreIR {

class SymbolTableInterface {
 public:
  virtual ~SymbolTableInterface() = default;

  virtual void setModuleName(
      std::string in_module_name, std::string out_module_name) = 0;
  virtual void setInstanceName(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_instance_name) = 0;
  virtual void setPortName(
      std::string in_module_name,
      std::string in_port_name,
      std::string out_module_name,
      std::string out_instance_name) = 0;

  virtual std::string getModuleName(std::string in_module_name) const = 0;
  virtual std::string getInstanceName(
      std::string in_module_name, std::string in_instance_name) const = 0;
  virtual std::pair<std::string, std::string> getPortName(
      std::string in_module_name, std::string in_port_name) const = 0;

  virtual ::nlohmann::json json() const = 0;
};

}  // namespace CoreIR
