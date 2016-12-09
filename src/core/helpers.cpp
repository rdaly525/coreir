#ifndef HELPERS_CPP_
#define HELPERS_CPP_

#include "enums.hpp"
#include <cassert>

using namespace std;

bool isNumber(string s) {
  return s.find_first_not_of("0123456789")==string::npos;
}

//TODO probably a better way of doing this with fancy macros
string wireableEnum2Str(WireableEnum wb) {
  switch(wb) {
    case IFACE: return "Interface";
    case INST: return "Instance";
    case SEL: return "Select";
    case TIFACE: return "TypedInterface";
    case TINST: return "TypedInstance";
    case TSEL: return "TypedSelect";
  }
  assert(false);
}


#endif //HELPERS_CPP_
