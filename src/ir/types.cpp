#include "coreir/ir/types.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/common.h"
#include "coreir/ir/error.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/value.h"

using namespace std;

namespace CoreIR {

void Type::print(void) { cout << "Type: " << (*this) << endl; }

string Type::TypeKind2Str(TypeKind t) {
  switch(t) {
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

Type* Type::sel(string selstr) {
  if (auto rt = dyn_cast<RecordType>(this)) {
    ASSERT(rt->getRecord().count(selstr),"Bad Select!");
    return rt->getRecord()[selstr];
  }
  else if (auto at = dyn_cast<ArrayType>(this)) {
    ASSERT(isNumber(selstr),selstr + " needs to be a number!");
    uint i = std::stoi(selstr,nullptr,0);
    ASSERT(i < at->getLen(),"Bad Select!");
    return at->getElemType();
  }
  ASSERT(0,"Bad Select");
}

bool Type::canSel(string selstr) {
  if (auto rt = dyn_cast<RecordType>(this)) {
    return rt->getRecord().count(selstr);
  }
  else if (auto at = dyn_cast<ArrayType>(this)) {
    if (!isNumber(selstr)) return false;
    uint i = std::stoi(selstr,nullptr,0);
    return i < at->getLen(); 
  }
  return false;
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

NamedType::NamedType(Namespace* ns, std::string name, Type* raw) : Type(TK_Named,raw->getDir(),ns->getContext()), RefName(ns,name), raw(raw) {}
NamedType::NamedType(Namespace* ns, string name, TypeGen* typegen, Values genargs) : Type(TK_Named,DK_Mixed,ns->getContext()), RefName(ns,name), typegen(typegen), genargs(genargs) {
  //Check args here.
  checkValuesAreParams(genargs,typegen->getParams());

  //Run the typegen
  raw = typegen->getType(genargs);
  dir = raw->getDir();
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
  
  RecordParams newParams({{label,t}});
  for (auto rparam : this->getRecord()) {
    newParams.push_back({rparam.first,rparam.second});
  }
  return c->Record(newParams);
}

Type* RecordType::detachField(string label) {
  ASSERT(this->getRecord().count(label)==1,"Cannot detach" + label + " from type: " + this->toString());
  
  RecordParams newParams;
  for (auto rparam : this->getRecord()) {
    if (rparam.first == label) continue;
    newParams.push_back({rparam.first,rparam.second});
  }
  return c->Record(newParams);
}

uint RecordType::getSize() const {
  uint size = 0;
  for (auto field : record) {
    size += field.second->getSize();
  }
  return size;
}

}//CoreIR namespace
