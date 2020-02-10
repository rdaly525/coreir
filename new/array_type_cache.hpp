#ifndef IR_ARRAY_TYPE_CACHE_HPP_
#define IR_ARRAY_TYPE_CACHE_HPP_

#include <map>
#include "array_type.hpp"
#include "contextual.hpp"

namespace CoreIR {

class CoreIRContextInterface;
class Type;

class ArrayTypeCache : Contextual {
 public:
  ArrayTypeCache(CoreIRContextInterface* Context) : Contextual(Context) {}

  std::shared_ptr<ArrayType> getOrInsert(int Size,
                                         std::shared_ptr<Type> ElementType);

 private:
  using KeyType = std::pair<int, Type*>;
  using MapType = std::map<KeyType, std::shared_ptr<ArrayType>>;

  MapType Cache;
};

}  // namespace CoreIR

#endif  // IR_ARRAY_TYPE_CACHE_HPP_
