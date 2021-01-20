#ifndef FLATTEN_HPP_
#define FLATTEN_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Flatten : public InstanceGraphPass {
 public:
  Flatten() : InstanceGraphPass("flatten", "Flattens everything!") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
