#include "types.hpp"
#include "typegen.hpp"

namespace CoreIR {

void Type::print(void) { cout << "Type: " << (*this) << endl; }

bool Type::sel(Context* c,string sel, Type** ret, Error* e) {
  *ret = c->Any(); 
  e->message("Cant select from this type!");
  e->message("  Type: " + toString());
  return true;
}

string Type::TypeKind2Str(TypeKind t) {
  switch(t) {
    case TK_Any : return "Any";
    case TK_Bit : return "Bit";
    case TK_BitIn : return "BitIn";
    case TK_Array : return "Array";
    case TK_Record : return "Record";
    case TK_Named : return "Named";
    default : return "NYI";
  }
}

std::ostream& operator<<(ostream& os, const Type& t) {
  os << t.toString();
  return os;
}

string RecordType::toString(void) const {
  string ret = "{";
  uint len = record.size();
  uint i=0;
  for(auto sel : _order) {
    ret += "'" + sel + "':" + record.at(sel)->toString();
    ret += (i==len-1) ? "}" : ", ";
    ++i;
  }
  return ret;
}

NamedType::NamedType(Namespace* ns, string name, TypeGen* typegen, Args genargs) : Type(TK_Named) ,ns(ns), name(name), typegen(typegen), genargs(genargs) {
  //Check args here.
  assert(checkArgs(genargs,typegen->getParams()));

  //Run the typegen
  raw = typegen->getType(genargs);
}

//TODO How to deal with select? For now just do a normal select off of raw
bool NamedType::sel(Context* c, string sel, Type** ret, Error* e) {
  return raw->sel(c,sel,ret,e);
}

bool AnyType::sel(Context* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  return false;
}

bool ArrayType::sel(Context* c, string sel, Type** ret, Error* e) {
  *ret = c->Any();
  if (!isNumber(sel)) {
    e->message("Idx into Array needs to be a number");
    e->message("  Idx: '" + sel + "'");
    e->message("  Type: " + toString());
    return true;
  }
  uint i = stoi(sel);
  if(i >= len ) {
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
bool RecordType::sel(Context* c, string sel, Type** ret, Error* e) {
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

}//CoreIR namespace
