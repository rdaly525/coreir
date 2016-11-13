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
string TypeEnum2Str(TypeEnum t) {
  switch(t) {
    case INT : return "Int";
    case ARRAY : return "Array";
    case RECORD : return "Record";
    default : return "BAD";
  }
}


string Type::getType(void) {return TypeEnum2Str(name);}
void Type::print(void) { cout << "Type: " << _string() << "\n"; }

uint32_t IntType::numBits(void) { return n;}
string IntType::_string() { 
  return Dir2Str(dir) + " " + Type::getType() + to_string(n);
}

string ArrayType::_string(void) { 
  return Type::getType() + "<" + baseType->_string() + ">[" + to_string(len) + "]";
}

string RecordType::_string(void) {
  string ret = "{";
  for(map<string,Type*>::iterator it=record.begin(); it!=record.end(); ++it) {
    ret += it->first + ":" + it->second->_string() + ",";
  }
  return ret + "}";
}
Type* RecordType::operator[](string sel) {
  return record[sel];
}

IntType* Int(uint bits, Dir dir) {
  return typecache.newInt(bits,dir);
}
//FloatType* Float(uint ebits, uint mbits, Dir dir);
//BoolType* Bool(Dir dir);
ArrayType* Array(Type* baseType, uint len) {
  return typecache.newArray(baseType,len);
}

//RecordType* Record(string key, Type* val,...);
//RecordType* AddField(RecordType* record, string key, Type* val);

//Type* Select(RecordType* iface, string key);
//Type* Flip(Type* type);
//


#endif //TYPES_CPP_
