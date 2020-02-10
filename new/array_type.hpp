#ifndef IR_ARRAY_TYPE_HPP_
#define IR_ARRAY_TYPE_HPP_

#include "type.hpp"

namespace CoreIR{

class ArrayType : public Type {
 public :
  ArrayType(CoreIRContextInterface* Context, int Size,
            std::shared_ptr<Type> ElementType)
      : Type(Context, TK_Array, ElementType->getDir()),
        Size(Size),
        ElementType(ElementType) {}

  std::string toString(void) const override { 
    return ElementType->toString() + "[" + std::to_string(Size) + "]";
  };
  int getSize() const override { return Size * ElementType->getSize(); }
  std::shared_ptr<Type> getElementType() const { return ElementType; }

 private:
  const int Size;
  std::shared_ptr<Type> ElementType;
};

}  // namespace CoreIR

#endif  // IR_ARRAY_TYPE_HPP_
