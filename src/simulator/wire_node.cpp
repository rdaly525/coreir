#include "wire_node.hpp"

namespace CoreIR {

  bool isGraphInput(const WireNode& w) {
    Wireable* base = w.getWire();

    if (isSelect(base) && fromSelf(toSelect(base))) {
      Type* tp = base->getType();
      // Inputs produce outputs
      return tp->isOutput();
    }

    return false;
  }

}
