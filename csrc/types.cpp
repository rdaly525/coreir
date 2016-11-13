#ifndef TYPES_CPP_
#define TYPES_CPP_


#include <iostream>
#include <string>
#include "types.hpp"
#include "typeCache.hpp"

using namespace std;

//Global cache
TypeCache typecache;

//TODO This should be done in a better way
string Dir2Str(Dir d) { if(d==IN) return "IN"; else return "OUT";}
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

uint32_t IntType::numBits(void) { return n;}
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
Type* ArrayType::idx() {
  return baseType;
}

string RecordType::_string(void) {
  string ret = "{";
  for(map<string,Type*>::iterator it=record.begin(); it!=record.end(); ++it) {
    ret += it->first + ":" + it->second->_string() + ",";
  }
  return ret + "}";
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
    return nullptr;
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

#endif //TYPES_CPP_
