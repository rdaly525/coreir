#ifndef HELPERS_CPP_
#define HELPERS_CPP_

#include "enums.hpp"
#include <cassert>

#include "coreir.hpp"
#include "typedcoreir.hpp"

using namespace std;

bool isNumber(string s) {
  return s.find_first_not_of("0123456789")==string::npos;
}

string TypeKind2Str(TypeKind t) {
  switch(t) {
    case INT : return "Int";
    case ARRAY : return "Array";
    case RECORD : return "Record";
    default : return "BAD";
  }
}

//TODO probably a better way of doing this with fancy macros
string wireableKind2Str(WireableKind wb) {
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

TypedWire* castTypedWire(Wire* w) {
  TypedWire* tw = dynamic_cast<TypedWire*>(w);
  if (!tw) {
    cout << "ERROR! Cannot cast to TypedWire!" <<endl;
    cout << "  Wire : " << w->toString() << endl;
    cout << "  Instantiable : " << *(w->getFrom()) << endl;
    assert(false);
  }
  return tw;
}
Type* wireable2Type(Wireable* w) {
  return castTypedWire(w->wire)->getType();
}
Dir flipDir(Dir d) { if(d==IN) return OUT; else return IN;}

#endif //HELPERS_CPP_
