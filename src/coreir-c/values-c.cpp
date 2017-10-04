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
  
  //Create Arg for Bool
  COREValue* COREValueBool(COREContext* cc, COREBool val) {
    Context* c = rcast<Context*>(cc);
    ConstPtr ga = Const::make(c,val);
    void* raw = c->saveValue(ga);
    return rcast<COREValue*>(raw);
  }
  
  //Create Value for int
  COREValue* COREValueInt(COREContext* cc,int i) {
    Context* c = rcast<Context*>(cc);
    ConstPtr ga = Const::make(c,i);
    void* raw = c->saveValue(ga);
    return rcast<COREValue*>(raw);
  }
  
  //Create Arg for String
  COREValue* COREValueString(COREContext* cc,char* str) {
    Context* c = rcast<Context*>(cc);
    ConstPtr ga = Const::make(c,string(str));
    void* raw = c->saveValue(ga);
    return rcast<COREValue*>(raw);
  }

}

}
