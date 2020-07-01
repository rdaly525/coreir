#ifndef COREIR_MARKDIRTY_HPP_
#define COREIR_MARKDIRTY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class MarkDirty : public ContextPass {
 public:
  MarkDirty() : ContextPass("markdirty", "Forces analysis passes to rerun") {}
  bool runOnContext(Context* c);
};

}  // namespace Passes
}  // namespace CoreIR

#endif
