#include "coreir/simulator/wire_node.h"

namespace CoreIR {

  bool isGraphOutput(const WireNode& w) {
    Wireable* base = w.getWire();

    if (isSelect(base) && fromSelf(toSelect(base))) {
      Type* tp = base->getType();
      // Inputs produce outputs
      return tp->isInput();
    }

    return false;

  }

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
