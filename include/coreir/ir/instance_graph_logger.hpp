#pragma once

#include <string>
#include <vector>
#include <variant>
#include "coreir/ir/json.h"
#include "coreir/ir/fwd_declare.h"

namespace CoreIR {

using InstancePath = SelectPath;

//Mapping[str inst, Union[str mname, Mapping[str inst, str inline_inst]]]

//                           Instance     Instance
using InlineEntry = std::map<std::string, std::string>;

//                             Instance                  Module
using ModuleStorage = std::map<std::string, std::variant<std::string, InlineEntry>>;

//This logger operates in two modes:
//  Construction: Constructs original graphs
//  Transforming: Modifies existing Modules
class InstanceGraphLogger {

  bool is_transform = false;
  //        Module
  std::map<std::string, ModuleStorage> storage;
  std::vector<std::string> log;

 public:
  InstanceGraphLogger() {}
  ~InstanceGraphLogger();

  void transform_mode() {this->is_transform = true;}
  void logInlineInstance(std::string parent, std::string i0, std::string i1, std::string inew);
  void logNewInstance(std::string parent, std::string child, std::string iname);
  void logRemoveInstance(std::string parent, std::string iname);

  InstancePath getInstancePath(std::string mname, InstancePath ipath);

  void print_log();
};


}  // namespace CoreIR
