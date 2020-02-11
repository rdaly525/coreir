#ifndef IR_BIT_IN_TYPE_HPP_
#define IR_BIT_IN_TYPE_HPP_

#include "type.hpp"

namespace CoreIR {

class BitInType : public Type {
 public:
  BitInType(CoreIRContextInterface* Context) : Type(Context, TK_BitIn, DK_In) {}

  std::string toString() const override { return "BitIn"; }
  int getSize() const override { return 1; }
};

}  // namespace CoreIR

#endif  // IR_BIT_IN_TYPE_HPP_
