#include "common.hpp"
#include <cassert>

//#include "coreir.hpp"
//#include "typedcoreir.hpp"
#include "args.hpp"

using namespace std;
namespace CoreIR {

Type* TypeGen::run(Context* c, Args args) {
  assert(checkParams(args,params));
  Type* ran = this->fun(c,args);
  return flipped ? c->Flip(ran) : ran;
}
bool isNumber(string s) {
  return s.find_first_not_of("0123456789")==string::npos;
}

string TypeKind2Str(TypeKind t) {
  switch(t) {
    case ANY : return "Any";
    case BITIN : return "BitIn";
    case BITOUT : return "BitOut";
    case ARRAY : return "Array";
    case RECORD : return "Record";
    default : return "NYI";
  }
}

string Param2Str(Param genparam) {
  switch(genparam) {
    case AINT : return "int";
    case ASTRING : return "string";
    case ATYPE : return "type";
    default : return "NYI";
  }
}
Param Str2Param(string s) {
  if (s=="int") return AINT;
  if (s=="string") return ASTRING;
  if (s=="type") return ATYPE;
  throw std::runtime_error("Cannot convert " + s + " to Param"); 
}

string Params2Str(Params genparams) {
  string ret = "(";
  for (auto it=genparams.begin(); it!=genparams.end(); ++it) {
    
    ret = ret + it->first + ": " + Param2Str(it->second) + ((it==genparams.begin()) ? "" : ",");
  }
  return ret + ")";
}

//TODO probably a better way of doing this with fancy macros
string wireableKind2Str(WireableKind wb) {
  switch(wb) {
    case IFACE: return "Interface";
    case INST: return "Instance";
    case SEL: return "Select";
  }
  assert(false);
}

} //CoreIR namespace
