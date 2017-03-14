#ifndef HELPERS_CPP_
#define HELPERS_CPP_

#include "common.hpp"
#include <cassert>

//#include "coreir.hpp"
//#include "typedcoreir.hpp"

using namespace std;

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

string GenParam2Str(GenParam genparam) {
  switch(genparam) {
    case GINT : return "int";
    case GSTRING : return "string";
    case GTYPE : return "type";
    default : return "NYI";
  }
}
GenParam Str2GenParam(string s) {
  if (s=="int") return GINT;
  if (s=="string") return GSTRING;
  if (s=="type") return GTYPE;
  throw std::runtime_error("Cannot convert " + s + " to GenParam"); 
}

string GenParams2Str(GenParams genparams) {
  string ret = "(";
  for (auto it=genparams.begin(); it!=genparams.end(); ++it) {
    
    ret = ret + it->first + ": " + GenParam2Str(it->second) + ((it==genparams.begin()) ? "" : ",");
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

#endif //HELPERS_CPP_
