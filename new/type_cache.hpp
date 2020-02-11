#ifndef IR_TYPE_CACHE_HPP_
#define IR_TYPE_CACHE_HPP_

#include <map>
#include <unordered_map>
#include "common.hpp"
#include "contextual.hpp"
#include "array_type.hpp"
#include "bit_type.hpp"
#include "bit_in_type.hpp"
#include "bit_in_out_type.hpp"
#include "record_type.hpp"

namespace CoreIR {

class CoreIRContextInterface;

using RecordArg = std::pair<std::string, std::shared_ptr<Type>>;

class TypeCache : Contextual {
 public:
  TypeCache(CoreIRContextInterface* Context);
  ~TypeCache() = default;

  std::shared_ptr<BitType> getBitType() { return Bit; }
  std::shared_ptr<BitInType> getBitInType() { return BitIn; }
  std::shared_ptr<BitInOutType> getBitInOutType() { return BitInOut; }
  std::shared_ptr<ArrayType> getArrayType(int Size,
                                          std::shared_ptr<Type> ElementType);
  std::shared_ptr<RecordType> getRecordType(
      const std::vector<RecordArg>& RecordArgs);

 private:
  struct RecordArgsHasher {
    std::size_t operator()(const std::vector<RecordArg>& Args) const {
      std::size_t Hash = 0;
      for (auto It : Args) {
        std::size_t Value = 0;
        common::HashCombine(It.first, &Value);
        common::HashCombine(It.second, &Value);
        Hash ^= Value;
      }
      return Hash;
    }
  };

  using ArrayTypeKey = std::pair<int, Type*>;
  using RecordTypeKey = std::vector<RecordArg>;

  std::shared_ptr<BitType> Bit;
  std::shared_ptr<BitInType> BitIn;
  std::shared_ptr<BitInOutType> BitInOut;
  std::map<ArrayTypeKey, std::shared_ptr<ArrayType>> ArrayTypeCache;
  std::unordered_map<RecordTypeKey,
                     std::shared_ptr<RecordType>,
                     RecordArgsHasher> RecordTypeCache;
};

}  // namespace CoreIR

#endif  // IR_TYPE_CACHE_HPP_
