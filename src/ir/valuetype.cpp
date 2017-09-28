#include "coreir/ir/valuetype.h"
#include "coreir/ir/context.h"

using namespace std;

namespace CoreIR {

std::string ValueType::toString() { 
  switch(kind) {
    case VTK_Bool : return "Bool";
    case VTK_Int : return "Int";
    case VTK_BitVector : return "BitVector(" + cast<BitVectorType>(this)->getWidth()+")";
    case VTK_String : return "String";
    case VTK_CoreIRType : return "CoreIRType";
    default : assert(0);
  }
}
static BoolType* BoolType::make(Context* c) {return c->typecache->getBool();}
static IntType* IntType::make(Context* c) {return c->typecache->getInt();}
static BitVectorType* BitVectorType::make(Context* c, int width) {return c->typecache->getBitVector(width);}
static StringType* StringType::make(Context* c) {return c->typecache->getString();}
static CoreIRType* CoreIRType::make(Context* c) {return c->typecache->getCoreIR();}

