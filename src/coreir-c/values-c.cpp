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

  bool COREValueBitVectorIsBinary(COREValue* a) {
    Value* value = rcast<Value*>(a);
    BitVector bv = value->get<BitVector>();
    return bv.is_binary();
  }

  void COREValueBitVectorGetWidth(COREValue* a, int* width) {
    Value* value = rcast<Value*>(a);
    BitVector bv = value->get<BitVector>();
    *width = bv.bitLength();
  }

  void COREValueBitVectorGet(COREValue* a, int* width, uint64_t* val) {
    Value* value = rcast<Value*>(a);
    BitVector bv = value->get<BitVector>();
    *width = bv.bitLength();
    *val = bv.to_type<uint64_t>();
  }

  void COREValueBitVectorGetString(COREValue* a, char *dst) {
    Value *value = rcast<Value*>(a);
    BitVector bv = value->get<BitVector>();
    string str = bv.hex_string();
    memcpy(dst, str.c_str(), str.size());
  }

  //Create Arg for Bool
  COREValue* COREValueBool(COREContext* cc, bool val) {
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

  COREValue* COREValueBitVectorString(COREContext* cc, char *str) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c, BitVector(string(str)));
    return rcast<COREValue*>(ga);
  }

  COREValue* COREValueModule(COREContext* cc, COREModule* mod) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c, rcast<Module*>(mod));
    return rcast<COREValue*>(ga);
  }

  COREValue* COREValueCoreIRType(COREContext* cc, COREType* type) {
    Context* c = rcast<Context*>(cc);
    Value* ga = Const::make(c, rcast<Type*>(type));
    return rcast<COREValue*>(ga);
  }

}

}
