#ifndef IR_NAMED_TYPE_HPP_
#define IR_NAMED_TYPE_HPP_

#include "type.hpp"

namespace CoreIR{

class NamedType : public Type {
 public:
  NamedType(CoreIRContextInterface* Context, std::shared_ptr<Type> Raw)
      : Type(Context, TK_Named, Raw->getDir()) {}

  // TODO(rsetaluri): Implement.
  std::string toString() const override { return ""; }
  int getSize() const override { return Raw->getSize();}

  std::shared_ptr<Type> getRaw() const { return Raw; }

 private:    
  std::shared_ptr<Type> Raw;
};

}  // namespace CoreIR

#endif  // IR_NAMED_TYPE_HPP_
