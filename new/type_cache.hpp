#ifndef IR_TYPE_CACHE_HPP_
#define IR_TYPE_CACHE_HPP_

#include "array_type_cache.hpp"
#include "contextual.hpp"
#include "bit_type.hpp"
#include "bit_in_type.hpp"
#include "bit_in_out_type.hpp"

namespace CoreIR {

class CoreIRContextInterface;

using RecordArg = std::pair<std::string, std::shared_ptr<Type>>;

class TypeCache : Contextual {
 public:
  TypeCache(CoreIRContextInterface* Context)
      : Contextual(Context),
        Bit(std::make_shared<BitType>(Context)),
        BitIn(std::make_shared<BitInType>(Context)),
        BitInOut(std::make_shared<BitInOutType>(Context)),
        ArrayCache(Context) {}

  std::shared_ptr<BitType> getBitType() { return Bit; }
  std::shared_ptr<BitInType> getBitInType() { return BitIn; }
  std::shared_ptr<BitInOutType> getBitInOutType() { return BitInOut; }
  std::shared_ptr<ArrayType> getArrayType(int Size,
                                          std::shared_ptr<Type> ElementType) {
    return ArrayCache.getOrInsert(Size, ElementType);
  }
  // TODO(rsetaluri): Implement this.
  std::shared_ptr<RecordType> getRecordType(std::vector<RecordArg> RecordArgs) {
    return std::shared_ptr<RecordType>(nullptr);
  }

 private:
  std::shared_ptr<BitType> Bit;
  std::shared_ptr<BitInType> BitIn;
  std::shared_ptr<BitInOutType> BitInOut;
  ArrayTypeCache ArrayCache;
};

}  // namespace CoreIR

#endif  // IR_TYPE_CACHE_HPP_
