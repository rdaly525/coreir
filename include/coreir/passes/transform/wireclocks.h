#ifndef WIRECLOCKPORTPASS_HPP_
#define WIRECLOCKPORTPASS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class WireClocks : public InstanceGraphPass {
 private:
  Type* clockType;
  void connectClk(ModuleDef* def, Wireable* topClk, Wireable* clk);

 public:
  WireClocks(std::string name, Type* clockType)
      : InstanceGraphPass(
          name,
          "Add a clock port to an instantiable if any of its instances contain "
          "an unwired clocked port. Also wires up the new clock port to the "
          "instances."),
        clockType(clockType) {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
