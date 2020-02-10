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
    return std::make_shared<BitType>(this);
  }
  std::shared_ptr<BitInType> BitIn() override {
    return std::make_shared<BitInType>(this);
  }
  std::shared_ptr<BitInOutType> BitInOut() override {
    return std::make_shared<BitInOutType>(this);
  }
  std::shared_ptr<ArrayType> Array(
      int Size,
      std::shared_ptr<Type> ElementType) override {
    return std::shared_ptr<ArrayType>(nullptr);
  }
  std::shared_ptr<RecordType> Record(
      std::vector<RecordArg> RecordArgs) override {
    return std::shared_ptr<RecordType>(nullptr);
  }
  std::shared_ptr<NamedType> Named(std::string NameRef) override {
    return std::shared_ptr<NamedType>(nullptr);
  }

 private:
  TypeCache TheTypeCache;
};

}  // namespace CoreIR

#endif  // IR_COREIR_CONTEXT_HPP_
