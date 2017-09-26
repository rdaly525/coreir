#include "coreir-c/coreir.h"
#include "coreir.h"

#include "common-c.hpp"

using namespace std;
namespace CoreIR {


extern "C" {

  COREParam COREGetArgKind(COREArg* arg) {
    Arg* t = rcast<Arg*>(arg);
    return static_cast<COREParam>(t->getKind());
  }
  
  int COREArgIntGet(COREArg* a) {
    Arg* arg = rcast<Arg*>(a);
    //Get will assert if wrong arg kind
    return arg->get<int>();
  }
  
  const char* COREArgStringGet(COREArg* a) {
    Arg* arg = rcast<Arg*>(a);
    //Get will assert if wrong arg kind
    const string& s = arg->get<string>();
    return s.c_str();
  }

  bool COREArgBoolGet(COREArg* a) {
    Arg* arg = rcast<Arg*>(a);
    //Get will assert if wrong arg kind
    return arg->get<bool>();
  }
  
  //Create Arg for int
  COREArg* COREArgInt(COREContext* c,int i) {
    ArgPtr ga = Const(i);
    void* raw = rcast<Context*>(c)->saveArg(ga);
    return rcast<COREArg*>(raw);
  }
  
  //Create Arg for String
  COREArg* COREArgString(COREContext* c,char* str) {
    ArgPtr ga = Const(string(str));
    void* raw = rcast<Context*>(c)->saveArg(ga);
    return rcast<COREArg*>(raw);
  }

  //Create Arg for Bool
  COREArg* COREArgBool(COREContext* c, bool val) {
    ArgPtr ga = Const(val);
    void* raw = rcast<Context*>(c)->saveArg(ga);
    return rcast<COREArg*>(raw);
  }

}

}
