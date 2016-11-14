#ifndef TYPES_CPP_
#define TYPES_CPP_


#include <iostream>
#include <string>
#include "types.hpp"
#include "typeCache.hpp"
#include <cassert>

using namespace std;

//Global cache
TypeCache typecache;

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

Type* IntType::flip(void) { 
  return typecache.newInt(n,flipDir(dir));
}

string ArrayType::_string(void) { 
  return Type::getType() + "<" + baseType->_string() + ">[" + to_string(len) + "]";
}

Type* ArrayType::flip(void) { 
  return typecache.newArray(baseType->flip(),len);
}
Type* ArrayType::idx(uint i) {
  if(i >= len) {
    cout << "ERROR: Index out of bounds\n";
    cout << "  idx: " << i << "\n";
    cout << "  ArrayLen: " << len << "\n";
    exit(0);
  }
  return baseType;
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

Type* RecordType::flip(void) { 
  map<string,Type*> m;
  map<string,Type*>::iterator it;
  for (it = record.begin(); it != record.end(); ++it) {
    m.emplace(it->first,it->second->flip());
  }
  return typecache.newRecord(m);
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

map<string,Type*> RecordType::get() {
  return record;
}

IntType* Int(uint bits, Dir dir) {
  return typecache.newInt(bits,dir);
}
//FloatType* Float(uint ebits, uint mbits, Dir dir);
//BoolType* Bool(Dir dir);
ArrayType* Array(Type* baseType, uint len) {
  return typecache.newArray(baseType,len);
}
RecordType* Record(map<string,Type*> record) {
  return typecache.newRecord(record);
}

RecordType* AddField(RecordType* record, string key, Type* val) {
  map<string,Type*> m = record->get();
  m.emplace(key,val);
  return typecache.newRecord(m);

}
Type* Sel(Type* record, string key) {
  if(!record->isType(RECORD)) {
    cout << "ERROR: Can only Sel on a record\n";
    cout << "  Type: " << record->getType() << "\n";
  }
  return ((RecordType*)record)->sel(key);
}
Type* Flip(Type* type) {
  return type->flip();
}

#endif //TYPES_CPP_
