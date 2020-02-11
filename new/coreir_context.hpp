#ifndef IR_COREIR_CONTEXT_HPP_
#define IR_COREIR_CONTEXT_HPP_

#include "array_type.hpp"
#include "bit_in_out_type.hpp"
#include "bit_in_type.hpp"
#include "bit_type.hpp"
#include "coreir_context_interface.hpp"
#include "named_type.hpp"
#include "record_type.hpp"
#include "type_cache.hpp"

namespace CoreIR {

using RecordArg = std::pair<std::string, std::shared_ptr<Type>>;

class CoreIRContext : public CoreIRContextInterface {
 public:
  CoreIRContext() : TheTypeCache(this) {}
  ~CoreIRContext() override = default;

  std::shared_ptr<BitType> Bit() override {
    return TheTypeCache.getBitType();
  }
  std::shared_ptr<BitInType> BitIn() override {
    return TheTypeCache.getBitInType();
  }
  std::shared_ptr<BitInOutType> BitInOut() override {
    return TheTypeCache.getBitInOutType();
  }
  std::shared_ptr<ArrayType> Array(
      int Size,
      std::shared_ptr<Type> ElementType) override {
    return TheTypeCache.getArrayType(Size, ElementType);
  }
  std::shared_ptr<RecordType> Record(
      const std::vector<RecordArg>& RecordArgs) override {
    return TheTypeCache.getRecordType(RecordArgs);
  }
  std::shared_ptr<NamedType> Named(std::string NameRef) override {
    return std::shared_ptr<NamedType>(nullptr);
  }

 private:
  TypeCache TheTypeCache;
};

}  // namespace CoreIR

#endif  // IR_COREIR_CONTEXT_HPP_
