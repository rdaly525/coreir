#ifndef TYPES_CPP_
#define TYPES_CPP_

#include "types.hpp"

void Type::print(void) { cout << "Type: " << (*this) << endl; }

bool Type::sel(CoreIRContext* c,string sel, Type** ret) {
  *ret = c->Any(); 
  c->newerror();
  c->error("Cant select from this type!");
  c->error("  Type: " + toString());
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

bool AnyType::sel(CoreIRContext* c, string sel, Type** ret) {
  *ret = c->Any();
  return false;
}
bool TypeGenType::sel(CoreIRContext* c, string sel, Type** ret) {
  *ret = c->Any();
  return false;
}

bool ArrayType::sel(CoreIRContext* c, string sel, Type** ret) {
  *ret = c->Any();
  if (!isNumber(sel)) {
    c->newerror();
    c->error("Idx into Array needs to be a number");
    c->error("  Idx: '" + sel + "'");
    c->error("  Type: " + toString());
    return true;
  }
  int i = stoi(sel);
  if (i <0 || i >= len ) {
    c->newerror();
    c->error("Index out of bounds for Array");
    c->error("  Required range: [0," + to_string(len-1) + "]");
    c->error("  Idx: " + sel);
    c->error("  Type: " + toString());
    return true;
  }
  *ret = elemType;
  return false;
}
 
// TODO should this actually return Any if it is missing?
bool RecordType::sel(CoreIRContext* c, string sel, Type** ret) {
  *ret = c->Any();
  auto it = record.find(sel);
  if (it != record.end()) {
    *ret = it->second;
    return false;
  } 
  c->newerror();
  c->error("Bad select field for Record");
  c->error("  Sel: '" + sel + "'");
  c->error("  Type: " + toString());
  return true;

}

#endif //TYPES_CPP_
