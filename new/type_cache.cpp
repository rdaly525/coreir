#include "type_cache.hpp"

namespace CoreIR {

TypeCache::TypeCache(CoreIRContextInterface* Context)
    : Contextual(Context),
      Bit(std::make_shared<BitType>(Context)),
      BitIn(std::make_shared<BitInType>(Context)),
      BitInOut(std::make_shared<BitInOutType>(Context)),
      ArrayTypeCache(),
      RecordTypeCache() {
  Bit->setFlipped(BitIn);
  BitIn->setFlipped(Bit);
  BitInOut->setFlipped(BitInOut);
}

std::shared_ptr<ArrayType> TypeCache::getArrayType(
    int Size,
    std::shared_ptr<Type> ElementType) {
  const auto Key = std::make_pair(Size, ElementType.get());
  auto It = ArrayTypeCache.find(Key);
  if (It != ArrayTypeCache.end()) return It->second;
  auto NewArrayType = std::make_shared<ArrayType>(getContext(), Size,
                                                  ElementType);
  ArrayTypeCache[Key] = NewArrayType;
  if (ElementType->isInOut()) {
    NewArrayType->setFlipped(NewArrayType);
  } else {
    auto FlippedElementType = ElementType->getFlipped();
    auto Flipped = std::make_shared<ArrayType>(getContext(), Size,
                                               FlippedElementType);
    NewArrayType->setFlipped(Flipped);
    auto FlippedKey = std::make_pair(Size, FlippedElementType.get());
    ArrayTypeCache[FlippedKey] = Flipped;
  }
  return NewArrayType;
}

std::shared_ptr<RecordType> TypeCache::getRecordType(
    std::vector<RecordArg> RecordArgs) {
  return std::shared_ptr<RecordType>(nullptr);  
}

}  // namespace CoreIR
