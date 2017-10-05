#include "coreir-c/coreir.h"
#include "coreir.h"

#include "common-c.hpp"

using namespace std;
namespace CoreIR {


extern "C" {

  COREValueType* COREGetValueType(COREValue* val) {
    Value* t = rcast<Value*>(val);
    return rcast<COREValueType*>(t->getKind());
  }
  
  int COREValueIntGet(COREValue* a) {
    Value* val = rcast<Value*>(a);
    //Get will assert if wrong val kind
    return val->get<int>();
  }
  
  const char* COREValueStringGet(COREValue* a) {
    Value* val = rcast<Value*>(a);
    //Get will assert if wrong val kind
    const string& s = val->get<string>();
    return s.c_str();
  }

  bool COREValueBoolGet(COREValue* a) {
    Value* val = rcast<Value*>(a);
    //Get will assert if wrong val kind
    return val->get<bool>();
  }

  void COREValueBitVectorGet(COREValue* a, int* width, uint64_t* val) {
    Value* value = rcast<Value*>(a);
    BitVector bv = value->get<BitVector>();
    *width = bv.bitLength();
    *val = bv.to_type<uint64_t>();
  }
  
  //Create Arg for Bool
  COREValue* COREValueBool(COREContext* cc, COREBool val) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c,val);
    return rcast<COREValue*>(ga);
  }
  
  //Create Value for int
  COREValue* COREValueInt(COREContext* cc,int i) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c,i);
    return rcast<COREValue*>(ga);
  }
  
  //Create Arg for String
  COREValue* COREValueString(COREContext* cc,char* str) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c,string(str));
    return rcast<COREValue*>(ga);
  }

  COREValue* COREValueBitVector(COREContext* cc, int width, uint64_t val) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c, width, val);
    return rcast<COREValue*>(ga);
  }

}

}
