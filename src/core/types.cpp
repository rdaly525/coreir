#ifndef TYPES_CPP_
#define TYPES_CPP_

#include "types.hpp"

void Type::print(void) { cout << "Type: " << (*this) << endl; }

std::ostream& operator<<(ostream& os, const Type& t) {
  os << t.toString();
  return os;
}

string RecordType::toString(void) const {
  string ret = "{";
  for(map<string,Type*>::const_iterator it=record.begin(); it!=record.end(); ++it) {
    ret += "'" + it->first + "':" + it->second->toString();
    ret += (it == --record.end()) ? "}" : ", ";
  }
  return ret;
}
TypeGenType::TypeGenType(TypeGen* def, GenArgs* args) : Type(TYPEGEN), def(def), args(args) {
  assert(args->checkKinds(def->kinds));
}

#endif //TYPES_CPP_
