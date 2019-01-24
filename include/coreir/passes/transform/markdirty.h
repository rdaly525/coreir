#ifndef COREIR_MARKDIRTY_HPP_
#define COREIR_MARKDIRTY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class MarkDirty : public ContextPass {
  public :
    static std::string ID;
    MarkDirty() : ContextPass(ID,"Forces analysis passes to rerun") {}
    bool runOnContext(Context* c);
};

}
}

#endif
