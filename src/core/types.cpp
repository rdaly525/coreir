#ifndef TYPES_CPP_
#define TYPES_CPP_


#include <iostream>
#include <string>
#include "types.hpp"
#include <cassert>

using namespace std;


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
string Type::getType(void) {return TypeEnum2Str(type);}
void Type::print(void) { cout << "Type: " << _string() << "\n"; }

uint IntType::numBits(void) { return n;}
string IntType::_string() { 
  return Dir2Str(dir) + " " + Type::getType() + to_string(n);
}

Type* IntType::flip(TypeCache* tc) {
  return tc->newInt(n,flipDir(dir));
}

string ArrayType::_string(void) { 
  return Type::getType() + "<" + elemType->_string() + ">[" + to_string(len) + "]";
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

RecordType::RecordType(map<string,Type*> record) : Type(RECORD,false), record(record) {
  for(map<string,Type*>::iterator it=record.begin(); it!=record.end(); ++it) {
    _hasInput |= it->second->hasInput();
  }
}
string RecordType::_string(void) {
  string ret = "{";
  for(map<string,Type*>::iterator it=record.begin(); it!=record.end(); ++it) {
    ret += it->first + ":" + it->second->_string();
    ret += (it == --record.end()) ? "}" : ", ";
  }
  return ret;
}

Type* RecordType::flip(TypeCache* tc) { 
  map<string,Type*> m;
  map<string,Type*>::iterator it;
  for (it = record.begin(); it != record.end(); ++it) {
    m.emplace(it->first,it->second->flip(tc));
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
    cout << "  type: " << _string() << "\n";
    exit(0);
  }
}



#endif //TYPES_CPP_
