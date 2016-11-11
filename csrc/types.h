#include <iostream>
#include <string>
#include <unordered_map>
using namespace std;

class Type {
  string type;
  public :
    Type(string _type) : type(_type) {}
    string getType(void);

};

class IntType : public Type {
  uint32_t n;
  public :
    IntType(uint32_t n) : Type("Int"), n(n) {}
    uint32_t numBits(void);
};

class ArrayType : public Type {
  Type baseType;
  uint32_t len;
  public :
    ArrayType(Type baseType, uint32_t len) : Type("Array"), baseType(baseType), len(len) {}
    
};

class RecordType : public Type {
  unordered_map<string,Type> record;
  public :
    RecordType(unordered_map<string,Type> record) : Type("Record"), record(record) {}

};
