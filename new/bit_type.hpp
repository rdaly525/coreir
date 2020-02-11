#ifndef IR_BIT_TYPE_HPP_
#define IR_BIT_TYPE_HPP_

#include "type.hpp"

namespace CoreIR {

class BitType : public Type {
 public:
  BitType(CoreIRContextInterface* Context) : Type(Context, TK_Bit, DK_Out) {}

  std::string toString() const override { return "Bit"; }
  int getSize() const override { return 1; }
};

}  // namespace CoreIR

#endif  // IR_BIT_TYPE_HPP_
