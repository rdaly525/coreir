#include <iostream>
#include <string>
#include <map>
using namespace std;

class Type {
  string type;
  public :
    Type(string _type) : type(_type) {}
    string getType(void);
    virtual string _string(void)=0;
    void print(void) { 
      cout << "Type: " << _string() << "\n";
    }
};

class IntType : public Type {
  uint32_t n;
  bool input;
  public :
    IntType(uint32_t n, bool input) : Type("Int"), n(n), input(input) {}
    uint32_t numBits(void);
    string _string() { 
      return (input ? "in " : "out ") + Type::getType() + to_string(n);
    }
};

class ArrayType : public Type {
  Type* baseType;
  uint32_t len;
  public :
    ArrayType(Type *baseType, uint32_t len) : Type("Array"), baseType(baseType), len(len) {}
    string _string(void) { 
      return Type::getType() + "<" + baseType->_string() + ">[" + to_string(len) + "]";
    }
};

class RecordType : public Type {
  map<string,Type*> record;
  public :
    RecordType(map<string,Type*> record) : Type("Record"), record(record) {}
    string _string(void) {
      string ret = "{";
      for(map<string,Type*>::iterator it=record.begin(); it!=record.end(); ++it) {
        ret = ret + it->first + ":" + it->second->_string() + ",";
      }
      return ret + "}";
    }
};


