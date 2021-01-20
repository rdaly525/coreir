#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class WireClocks : public InstanceGraphPass {
 private:
  Type* clockType;
  std::string port_name;
  void connectClk(ModuleDef* def, Wireable* topClk, Wireable* clk);

 public:
  WireClocks(std::string name, Type* clockType, std::string port_name)
      : InstanceGraphPass(
          name,
          "Add a clock port to an instantiable if any of its instances contain "
          "an unwired clocked port. Also wires up the new clock port to the "
          "instances."),
        clockType(clockType), port_name(port_name) {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
