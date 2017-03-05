#ifndef TYPES_CPP_
#define TYPES_CPP_

#include "types.hpp"

void Type::print(void) { cout << "Type: " << (*this) << endl; }

bool Type::sel(CoreIRContext* c,string sel, Type** ret, Error* e) {
  *ret = c->Any(); 
  e->message("Cant select from this type!");
  e->message("  Type: " + toString());
  return true;
}

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
  assert(args->checkKinds(def->argkinds));
}

bool AnyType::sel(CoreIRContext* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  return false;
}
bool TypeGenType::sel(CoreIRContext* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  return false;
}

bool ArrayType::sel(CoreIRContext* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  if (!isNumber(sel)) {
    e->message("Idx into Array needs to be a number");
    e->message("  Idx: '" + sel + "'");
    e->message("  Type: " + toString());
    return true;
  }
  int i = stoi(sel);
  if (i <0 || i >= len ) {
    e->message("Index out of bounds for Array");
    e->message("  Required range: [0," + to_string(len-1) + "]");
    e->message("  Idx: " + sel);
    e->message("  Type: " + toString());
    return true;
  }
  *ret = elemType;
  return false;
}
 
// TODO should this actually return Any if it is missing?
bool RecordType::sel(CoreIRContext* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  auto it = record.find(sel);
  if (it != record.end()) {
    *ret = it->second;
    return false;
  } 
  e->message("Bad select field for Record");
  e->message("  Sel: '" + sel + "'");
  e->message("  Type: " + toString());
  return true;

}

#endif //TYPES_CPP_
