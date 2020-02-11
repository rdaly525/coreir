#ifndef IR_COREIR_CONTEXT_INTERFACE_HPP_
#define IR_COREIR_CONTEXT_INTERFACE_HPP_

namespace CoreIR {

class BitType;
class BitInType;
class BitInOutType;
class ArrayType;
class RecordType;
class NamedType;
class Type;

using RecordArg = std::pair<std::string, std::shared_ptr<Type>>;

class CoreIRContextInterface {
 public:
  CoreIRContextInterface() = default;
  virtual ~CoreIRContextInterface() = default;

  virtual std::shared_ptr<BitType> Bit() = 0;
  virtual std::shared_ptr<BitInType> BitIn() = 0;
  virtual std::shared_ptr<BitInOutType> BitInOut() = 0;
  virtual std::shared_ptr<ArrayType> Array(
      int Size,
      std::shared_ptr<Type> ElementType) = 0;
  virtual std::shared_ptr<RecordType> Record(
      const std::vector<RecordArg>& RecordArgs) = 0;
  virtual std::shared_ptr<NamedType> Named(std::string NameRef) = 0;
};

}  // namespace CoreIR

#endif  // IR_COREIR_CONTEXT_INTERFACE_HPP_
