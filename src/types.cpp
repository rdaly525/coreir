#include "types.hpp"
#include "typegen.hpp"

namespace CoreIR {

void Type::print(void) { cout << "Type: " << (*this) << endl; }

bool Type::sel(string sel, Type** ret, Error* e) {
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

Type* Type::Arr(uint i) {
  return c->Array(i,this);
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

NamedType::NamedType(Context* c,Namespace* ns, string name, TypeGen* typegen, Args genargs) : Type(TK_Named,DK_Mixed,c) ,ns(ns), name(name), typegen(typegen), genargs(genargs) {
  //Check args here.
  checkArgsAreParams(genargs,typegen->getParams());

  //Run the typegen
  raw = typegen->getType(genargs);
  dir = raw->getDir();
}

//TODO How to deal with select? For now just do a normal select off of raw
bool NamedType::sel(string sel, Type** ret, Error* e) {
  return raw->sel(sel,ret,e);
}

bool AnyType::sel(string sel, Type** ret, Error* e) {
  *ret = c->Any();
  return false;
}

bool ArrayType::sel(string sel, Type** ret, Error* e) {
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

//Stupid hashing wrapper for enum
RecordType::RecordType(Context* c, RecordParams _record) : Type(TK_Record,DK_Unknown,c) {
  unordered_set<uint> dirs; // Slight hack because it is not easy to hash enums
  for(auto field : _record) {
    assert(!isNumber(field.first) && "Cannot have number as record field");
    record.emplace(field.first,field.second);
    _order.push_back(field.first);
    dirs.insert(field.second->getDir());
  }
  if (dirs.count(DK_Unknown)) {
    dir = DK_Unknown;
  }
  else if (dirs.size() > 1) {
    dir = DK_Mixed;
  }
  else {
    dir = (DirKind) *(dirs.begin());
  }
}

void RecordType::addItem(string s, Type* t) {
  bool first = _order.empty();
  _order.push_back(s);
  record.emplace(s,t);
  DirKind tDir = t->getDir();
  //This logic is a bit sketch. Should probably test this a lot
  if (first) {
    dir = tDir;
  }
  else if (dir==DK_Unknown || tDir==DK_Unknown) {
    dir = DK_Unknown;
  }
  else if (dir==DK_Mixed || tDir==DK_Mixed || dir !=tDir) {
    dir = DK_Mixed;
  }
}

// TODO should this actually return Any if it is missing?
bool RecordType::sel(string sel, Type** ret, Error* e) {
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
