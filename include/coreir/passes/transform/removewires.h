#ifndef REMOVEWIRES_H_
#define REMOVEWIRES_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveWires : public InstanceVisitorPass {
 public:
  RemoveWires() : InstanceVisitorPass("removewires", "Inlines all wires") {}
  void setVisitorInfo() override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
