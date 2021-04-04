#pragma once

#include <string>
#include <utility>
#include "coreir/ir/json.h"

namespace CoreIR {

class SymbolTableInterface;

class SymbolTableSentinel {
 public:
  explicit SymbolTableSentinel(std::string flag) : flag(flag) {}
  ~SymbolTableSentinel() = default;

  const std::string& getFlag() const { return flag; }

 private:
  const std::string flag;
};

class SymbolTableLoggerInterface {
 public:
  class DebugIterator {
   public:
    virtual ~DebugIterator() = default;
    virtual bool next() = 0;
    virtual std::string debugString() const = 0;
  };
  SymbolTableLoggerInterface(SymbolTableInterface* table) : table(table) {}
  virtual ~SymbolTableLoggerInterface() = default;
  virtual void logNewInstance(
      std::string module_name,
      std::string instance_type,
      std::string instance_name) = 0;
  virtual void logRemoveInstance(
      std::string module_name, std::string instance_name) = 0;
  virtual void logRenameInstance(
      std::string module_name,
      std::string instance_name,
      std::string new_instance_name) = 0;
  virtual void logInlineInstance(
      std::string module_name,
      std::string instance_name,
      std::string instance_type,
      std::string child_instance_name,
      std::string child_instance_type,
      std::string new_instance_name) = 0;
  virtual void pauseLogging() = 0;
  virtual void resumeLogging() = 0;
  virtual bool finalize() = 0;

  virtual std::unique_ptr<DebugIterator> debugIterator() const = 0;

 protected:
  SymbolTableInterface* table;
};

class SymbolTableInterface {
 public:
  using InstanceNameType = std::tuple<
   SymbolTableSentinel const*, std::string>;

  virtual ~SymbolTableInterface() = default;

  virtual void setModuleName(
      std::string in_module_name, std::string out_module_name) = 0;
  virtual void setInstanceName(
      std::string in_module_name,
      std::string in_instance_name,
      InstanceNameType out_instance_name) = 0;
  virtual void setPortName(
      std::string in_module_name,
      std::string in_port_name,
      std::string out_instance_name) = 0;
  virtual void setInlinedInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name,
      InstanceNameType out_instance_name) = 0;
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

  virtual SymbolTableLoggerInterface* getLogger() = 0;
  virtual bool finalizeLogger() = 0;

  virtual ::nlohmann::json json() const = 0;
};

}  // namespace CoreIR
