#ifndef IR_ARRAY_TYPE_CACHE_HPP_
#define IR_ARRAY_TYPE_CACHE_HPP_

#include "array_type.hpp"
#include "contextual.hpp"

namespace CoreIR {

class CoreIRContextInterface;
class Type;

class ArrayTypeCache : Contextual {
 public:
  ArrayTypeCache(CoreIRContextInterface* Context) : Contextual(Context) {}

  // TODO(rsetaluri): Move to .cpp file.
  std::shared_ptr<ArrayType> getOrInsert(int Size,
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

 private:
  using KeyType = std::pair<int, Type*>;
  using MapType = std::map<KeyType, std::shared_ptr<ArrayType>>;

  MapType Cache;
};

}  // namespace CoreIR

#endif  // IR_ARRAY_TYPE_CACHE_HPP_
