#ifndef TYPES_CPP_
#define TYPES_CPP_

#include "types.hpp"

void Type::print(void) { cout << "Type: " << (*this) << endl; }

bool Type::sel(CoreIRContext* c,string sel, Type** ret) {*ret = c->Any(); return true;}
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
  if (!isNumber(sel)) return true;
  int i = stoi(sel);
  if (i <0 || i >= len ) return true;
  *ret = elemType;
  return false;
}
 
// TODO should this actually return Any if it is missing?
bool RecordType::sel(CoreIRContext* c, string sel, Type** ret) {
  *ret = c->Any();
  cout << "Record Sel: " << sel << endl;
  auto it = record.find(sel);
  if (it != record.end()) {
    cout << "Found! " << *(it->second) << endl;
    *ret = it->second;
    return false;
  } 
  return true;
               //cout << "ERROR: Bad select field\n";
               //    //cout << "  sel: " << a << "\n";
               //        //cout << "  kind: " << (*this) << "\n";
               //            //exit(0);
               //              }

}

#endif //TYPES_CPP_
