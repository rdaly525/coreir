#include "coreir/passes/transform/flattentypes2.h"

bool isBitOrNDArrOfBits(CoreIR::Type* t) {
  if (isBit(t)) return true;
  if (auto at = CoreIR::dyn_cast<CoreIR::ArrayType>(t)) {
    return isBitOrNDArrOfBits(at->getElemType());
  }
  return false;
}

bool CoreIR::Passes::FlattenTypes2::isLeafType(Type* t) {
  return isBitOrNDArrOfBits(t);
}
