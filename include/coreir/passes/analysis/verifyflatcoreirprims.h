#ifndef VERIFYFLATCOREIRPRIMS_H_
#define VERIFYFLATCOREIRPRIMS_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class VerifyFlatCoreirPrims : public InstanceGraphPass {
 public:
  VerifyFlatCoreirPrims()
      : InstanceGraphPass(
          "verifyflatcoreirprims",
          "Verify all instances have been flattened",
          true) {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
}; /* class VerifyFlatCoreirPrims */

}  // namespace Passes
}  // namespace CoreIR

#endif
