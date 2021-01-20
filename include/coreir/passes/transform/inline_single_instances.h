#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class InlineSingleInstances : public InstanceGraphPass {
 public:
  InlineSingleInstances()
      : InstanceGraphPass(
          "inline_single_instances",
          "Inlines any modules that contains a single instance") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
