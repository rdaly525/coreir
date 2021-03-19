#pragma once

#include <string>
#include <vector>
#include <variant>
#include "coreir/ir/json.h"
#include "coreir/ir/fwd_declare.h"

namespace CoreIR {

using InstancePath = SelectPath;

struct InstInfo {
  std::string module;
  bool is_inlined = false;
  //       sub_inst      new_inst
  std::map<std::string, std::string> inline_info;
  InstInfo(std::string module) : module(module) {}
};

class InstanceGraphLogger {

  bool is_transform = false;
  //        Module -> Inst -> InstInfo
  std::map<std::string, std::map<std::string, InstInfo>> storage;
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
