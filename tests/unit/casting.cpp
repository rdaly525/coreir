#include "coreir.h"
#include <cassert>

using namespace CoreIR;

int main() {
  Context* c = newContext();
  
  //Any
  {
    Type* t = c->Any();
    assert(isa<AnyType>(t));
    AnyType* at = cast<AnyType>(t);
    at->print();
    if (auto dt = dyn_cast<Type>(at)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<AnyType>(t)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<BitType>(t)) {
      assert(0);
      dt->print();
    }
  }
  
  //Bit
  {
    Type* t = c->Bit();
    t->print();
    assert(isa<BitType>(t));
    BitType* at = cast<BitType>(t);
    at->print();
    if (auto dt = dyn_cast<Type>(at)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<BitType>(t)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<RecordType>(t)) {
      assert(0);
      dt->print();
    }
  }
  
  //Array
  {
    Type* t = c->Array(5,c->Array(3,c->BitIn()));
    t->print();
    assert(isa<ArrayType>(t));
    ArrayType* at = cast<ArrayType>(t);
    at->print();
    if (auto dt = dyn_cast<Type>(at)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<ArrayType>(t)) {
      assert(1);
      dt->print();
    }
    if (auto dt = dyn_cast<RecordType>(t)) {
      assert(0);
      dt->print();
    }
  }
  
  deleteContext(c);

}
