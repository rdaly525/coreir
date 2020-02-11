#ifndef IR_CONTEXTUAL_HPP_
#define IR_CONTEXTUAL_HPP_

namespace CoreIR {

class CoreIRContextInterface;

// Base class for holding a non-owning reference (pointer) to a CoreIR context.
class Contextual {
 public:
  Contextual(CoreIRContextInterface* Context) : Context(Context) {}

  CoreIRContextInterface* getContext() { return Context; }
  const CoreIRContextInterface* getContext() const { return Context; }

 private:
  CoreIRContextInterface* Context;
};

}  // namespace CoreIR

#endif  // IR_CONTEXTUAL_HPP_
