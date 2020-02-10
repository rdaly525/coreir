#include "type_cache.hpp"

namespace CoreIR {

std::shared_ptr<ArrayType> TypeCache::getArrayType(
    int Size,
    std::shared_ptr<Type> ElementType) {
  const auto Key = std::make_pair(Size, ElementType.get());
  auto It = ArrayTypeCache.find(Key);
  if (It != ArrayTypeCache.end()) return It->second;
  if (ElementType->isInOut()) {
    auto NewArrayType = std::make_shared<ArrayType>(getContext(), Size,
                                                    ElementType);
    // TODO(rsetaluri): Set flipped.
    ArrayTypeCache[Key] = NewArrayType;
    return NewArrayType;
  }
  auto NewArrayType = std::make_shared<ArrayType>(getContext(), Size,
                                                  ElementType);
  // TODO(rsetaluri): Set flipped.
  ArrayTypeCache[Key] = NewArrayType;
  return NewArrayType;
}

std::shared_ptr<RecordType> TypeCache::getRecordType(
    std::vector<RecordArg> RecordArgs) {
  return std::shared_ptr<RecordType>(nullptr);  
}

}  // namespace CoreIR
