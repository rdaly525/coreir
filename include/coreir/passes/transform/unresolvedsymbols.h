#ifndef COREIR_UNRESOLVED_HPP_
#define COREIR_UNRESOLVED_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class UnresolvedSymbols : public ContextPass {
 public:
  UnresolvedSymbols()
      : ContextPass("unresolved", "outputs all unresolved symbols") {}
  bool runOnContext(Context* c);
};

}  // namespace Passes
}  // namespace CoreIR

#endif
