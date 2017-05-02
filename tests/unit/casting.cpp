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
    assert(dyn_cast<Type>(at));
    assert(dyn_cast<AnyType>(t));
    assert(!dyn_cast<BitType>(t));
  }
  
  //Bit
  {
    Type* t = c->Bit();
    assert(isa<BitType>(t));
    BitType* at = cast<BitType>(t);
    assert(dyn_cast<Type>(at));
    assert(dyn_cast<BitType>(t));
    assert(!dyn_cast<RecordType>(t));
  }
  
  //Array
  {
    Type* t = c->Array(5,c->Array(3,c->BitIn()));
    assert(isa<ArrayType>(t));
    ArrayType* at = cast<ArrayType>(t);
    assert(dyn_cast<Type>(at));
    assert(dyn_cast<ArrayType>(t));
    assert(!dyn_cast<RecordType>(t));
  }
  

  //Test casting of ArgInt
  {
    Arg* a = c->argInt(5);
    assert(isa<ArgInt>(a));
    assert(a->get<ArgInt>()==5);
    ArgInt* ac = cast<ArgInt>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgInt>(a));
    assert(!dyn_cast<ArgString>(a));
  }
  
  //Test casting of ArgString
  {
    Arg* a = c->argString("Ross");
    assert(isa<ArgString>(a));
    assert(a->get<ArgString>()=="Ross");
    ArgString* ac = cast<ArgString>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgString>(a));
    assert(!dyn_cast<ArgType>(a));
  }
  
  //Test casting of ArgType
  {
    Arg* a = c->argType(c->BitIn());
    assert(isa<ArgType>(a));
    assert(a->get<ArgType>()==c->BitIn());
    ArgType* ac = cast<ArgType>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgType>(a));
    assert(!dyn_cast<ArgInt>(a));
  }


  deleteContext(c);

}
