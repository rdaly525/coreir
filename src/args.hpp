#ifndef GENARGS_HPP_
#define GENARGS_HPP_


#include "types.hpp"
#include "common.hpp"
#include <cassert>
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

//struct Params {
//  unordered_map<string,Param> dict;
//  Params(unordered_map<string,Param> dict) : dict(dict) {}
//  Param operator[](const string& key) {
//    //What should I do if this is not valid?
//    return dict[key];
//  }
//}

namespace CoreIR {

struct Arg {
  virtual ~Arg() {}
  Param kind;
  Arg(Param kind) : kind(kind) {}
  bool isKind(Param k) { return kind==k; }
  int arg2Int();
  string arg2String();
  Type* arg2Type();
  
  virtual json toJson()=0;
};

struct GenString : Arg {
  string str;
  GenString(string str) : Arg(ASTRING), str(str) {}
  json toJson();
};

struct GenInt : Arg {
  int i;
  GenInt(int i) : Arg(AINT), i(i) {}
  json toJson();
};

struct GenType : Arg {
  Type* t;
  GenType(Type* t) : Arg(ATYPE), t(t) {}
  json toJson();
};


//class Instantiable;
//struct GenInst : Arg {
//  Instantiable* i;
//  GenInst(Instantiable* i) : Arg(GINST), i(i) {}
//};

struct Args {
  Context* c;
  unordered_map<string,Arg*> args;
  Args(Context* c, unordered_map<string,Arg*> args=unordered_map<string,Arg*>()) : c(c), args(args) {}
  void addField(string s, Arg* arg) { args[s] = arg;}
  json toJson();
  Arg* operator[](const string s) const;
  void print() {
    for (auto arg : args) cout << " Arg: " << arg.first << endl;
  }
  bool ArgEq(Arg* a, Arg* b);

  bool checkParams(Params kinds) {
    if (args.size() != kinds.size()) return false;
    for (auto field : args) {
      auto kind = kinds.find(field.first);
      if (kind == kinds.end()) return false;
      assert(kind->first == field.first);
      if (! field.second->isKind(kind->second) ) return false;
    }
    return true;
  }
  bool operator==(const Args r) {
    if (args.size() != r.args.size()) return false;
    for (auto field : args) {
      auto rfield = r.args.find(field.first);
      if(rfield == r.args.end()) return false;
      if (!ArgEq(field.second,rfield->second)) return false;
    }
    return true;
  }
  bool operator!=(Args r) {
    return !(*this == r);
  }
};

}//CoreIR namespace


namespace std {
  template<>
  struct hash<CoreIR::Args> {
    size_t operator() (const CoreIR::Args& p) const;
  };
}



#endif //GENARGS_HPP_
