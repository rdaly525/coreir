#ifndef HELPERS_CPP_
#define HELPERS_CPP_

#include "enums.hpp"
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

string ArgKind2Str(ArgKind argkind) {
  switch(argkind) {
    case GINT : return "int";
    case GSTRING : return "string";
    case GTYPE : return "type";
  }
}

string ArgKinds2Str(ArgKinds argkinds) {
  string ret = "(";
  for (auto it=argkinds.begin(); it!=argkinds.end(); ++it) {
    ret = ret + ArgKind2Str(*it) + ((it==argkinds.begin()) ? "" : ",");
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
