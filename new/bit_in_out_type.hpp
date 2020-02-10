#ifndef IR_BIT_IN_OUT_TYPE_HPP_
#define IR_BIT_IN_OUT_TYPE_HPP_

#include "type.hpp"

namespace CoreIR{

class BitInOutType : public Type {
 public:
  BitInOutType(CoreIRContextInterface* Context)
      : Type(Context, TK_BitInOut, DK_InOut) {}

  std::string toString() const override { return "BitInOut"; }
  int getSize() const override { return 1; }
};

}  // namespace CoreIR

#endif  // IR_BIT_IN_OUT_TYPE_HPP_
