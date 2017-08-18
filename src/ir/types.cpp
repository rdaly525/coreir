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

bool Type::isBaseType() {return isa<BitType>(this) || isa<BitInType>(this);}

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
  if (dirs.count(DK_Unknown) || dirs.size()==0) {
    dir = DK_Unknown;
  }
  else if (dirs.size() > 1) {
    dir = DK_Mixed;
  }
  else {
    dir = (DirKind) *(dirs.begin());
  }
}

Type* RecordType::appendField(string label, Type* t) {
  ASSERT(this->getRecord().count(label)==0,"Cannot append " + label + " to type: " + this->toString());
  
  //TODO this was annoying to write. I should fix up the whole myPair thing
  RecordParams newParams({myPair<string,Type*>(label,t)});
  for (auto rparam : this->getRecord()) {
    newParams.push_back(myPair<string,Type*>(rparam.first,rparam.second));
  }
  return c->Record(newParams);
}

Type* RecordType::detachField(string label) {
  ASSERT(this->getRecord().count(label)==1,"Cannot detach" + label + " from type: " + this->toString());
  
  //TODO this was annoying to write. I should fix up the whole myPair thing
  RecordParams newParams;
  for (auto rparam : this->getRecord()) {
    if (rparam.first == label) continue;
    newParams.push_back(myPair<string,Type*>(rparam.first,rparam.second));
  }
  return c->Record(newParams);
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
uint RecordType::getSize() const {
  uint size = 0;
  for (auto field : record) {
    size += field.second->getSize();
  }
  return size;
}

}//CoreIR namespace
