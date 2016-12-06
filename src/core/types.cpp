#ifndef TYPES_CPP_
#define TYPES_CPP_


#include <iostream>
#include <string>
#include "types.hpp"
#include <cassert>

using namespace std;


ostream& operator<<(ostream& os, const Type& t) {
  os << t.toString();
  return os;
}

//TODO This should be done in a better way
string Dir2Str(Dir d) { if(d==IN) return "In"; else return "Out";}
Dir flipDir(Dir d) { if(d==IN) return OUT; else return IN;}
string TypeEnum2Str(TypeEnum t) {
  switch(t) {
    case INT : return "Int";
    case ARRAY : return "Array";
    case RECORD : return "Record";
    default : return "BAD";
  }
}


bool Type::isType(TypeEnum t) {
  return t==type;
}

void Type::print(void) { cout << "Type: " << (*this) << endl; }

string IntType::toString(void) const { 
  return Dir2Str(dir) + " " + TypeEnum2Str(this->type) + to_string(n);
}

Type* IntType::flip(TypeCache* tc) {
  return tc->newInt(n,flipDir(dir));
}

string ArrayType::toString(void) const { 
  return TypeEnum2Str(this->type) + "<" + elemType->toString() + ">[" + to_string(len) + "]";
}

Type* ArrayType::flip(TypeCache* tc) { 
  return tc->newArray(elemType->flip(tc),len);
}
Type* ArrayType::idx(uint i) {
  if(i >= len) {
    cout << "ERROR: Index out of bounds\n";
    cout << "  idx: " << i << "\n";
    cout << "  ArrayLen: " << len << "\n";
    exit(0);
  }
  return elemType;
}

string RecordType::toString(void) const {
  string ret = "{";
  for(map<string,Type*>::const_iterator it=record.begin(); it!=record.end(); ++it) {
    ret += it->first + ":" + it->second->toString();
    ret += (it == --record.end()) ? "}" : ", ";
  }
  return ret;
}

Type* RecordType::flip(TypeCache* tc) { 
  recordparam_t m;
  for (vector<string>::iterator it=_order.begin(); it!=_order.end(); ++it) {
    map<string,Type*>::iterator tit = record.find(*it);
    assert(tit!=record.end());
    m.push_back({(*it),tit->second->flip(tc)});
  }
  return tc->newRecord(m);
}

//What to return if did not find?
Type* RecordType::sel(string a) {
  map<string,Type*>::iterator it = record.find(a);
  if (it != record.end()) {
    return it->second;
  } else {
    cout << "ERROR: Bad select field\n";
    cout << "  sel: " << a << "\n";
    cout << "  type: " << (*this) << "\n";
    exit(0);
  }
}



#endif //TYPES_CPP_
