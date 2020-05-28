#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class InlineSingleInstances : public InstanceGraphPass {
 public:
  static std::string ID;
  InlineSingleInstances()
      : InstanceGraphPass(
          ID,
          "Inlines any modules that contains a single instance") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
