#ifndef COREIR_UNRESOLVED_HPP_
#define COREIR_UNRESOLVED_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {


class UnresolvedSymbols : public ContextPass {
  public :
    static std::string ID;
    UnresolvedSymbols() : ContextPass(ID,"outputs all unresolved symbols") {}
    bool runOnContext(Context* c);
};

}
}

#endif
