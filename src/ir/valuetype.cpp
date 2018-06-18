#include "coreir/ir/valuetype.h"
#include "coreir/ir/context.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/typecache.h"

using namespace std;

namespace CoreIR {

std::string ValueType::toString() { 
  switch(kind) {
    case VTK_Bool : return "Bool";
    case VTK_Int : return "Int";
    case VTK_BitVector : return "BitVector<" + to_string(cast<BitVectorType>(this)->getWidth())+">";
    case VTK_String : return "String";
    case VTK_CoreIRType : return "CoreIRType";
    case VTK_Module : return "Module";
    case VTK_Json : return "Json";
    case VTK_Any : return "Any";
    default : assert(0);
  }
}
AnyType* AnyType::make(Context* c) {return c->typecache->getAny();}
BoolType* BoolType::make(Context* c) {return c->typecache->getBool();}
IntType* IntType::make(Context* c) {return c->typecache->getInt();}
BitVectorType* BitVectorType::make(Context* c, int width) {return c->typecache->getBitVector(width);}
StringType* StringType::make(Context* c) {return c->typecache->getString();}
CoreIRType* CoreIRType::make(Context* c) {return c->typecache->getCoreIRType();}
ModuleType* ModuleType::make(Context* c) {return c->typecache->getModuleType();}
JsonType* JsonType::make(Context* c) {return c->typecache->getJsonType();}

}
