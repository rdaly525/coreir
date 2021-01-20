#ifndef REMOVEUNCONNECTED_HPP_
#define REMOVEUNCONNECTED_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveUnconnected : public InstancePass {
 public:
  RemoveUnconnected()
      : InstancePass("removeunconnected", "Removes unconnected Instances") {}
  bool runOnInstance(Instance* i) override;
};

}  // namespace Passes
}  // namespace CoreIR
#endif
