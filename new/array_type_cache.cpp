#include "array_type_cache.hpp"

namespace CoreIR {

std::shared_ptr<ArrayType> ArrayTypeCache::getOrInsert(
    int Size,
    std::shared_ptr<Type> ElementType) {
  // We get the raw pointer of the underlying element just for the sake of
  // forming the key for the cache.
  const auto Key = std::make_pair(Size, ElementType.get());
  const auto it = Cache.find(Key);
  if (it != Cache.end()) return it->second;
  auto NewArrayType = std::make_shared<ArrayType>(getContext(), Size,
                                                  ElementType);
  Cache[Key] = NewArrayType;
  return NewArrayType;
}

}  // namespace CoreIR
