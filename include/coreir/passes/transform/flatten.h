#ifndef FLATTEN_HPP_
#define FLATTEN_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Flatten : public InstanceGraphPass {
  // Inlining doesn't handle slices, for now we insert a wire node before slice
  // connections so the existing inlining logic works.  We cache the result of
  // the transformation so we only do this insertion once per module definition
  std::map<ModuleDef*, ModuleDef*> moduleDefsWithWiresForSlicesCache;

 public:
  static std::string ID;
  Flatten() : InstanceGraphPass(ID, "Flattens everything!") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
