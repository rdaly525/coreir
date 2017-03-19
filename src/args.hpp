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
  virtual bool operator==(const Arg& r) const=0 {
    return r->isKind(kind);
  }
};

struct ArgInt : Arg {
  int i;
  ArgInt(int i) : Arg(AINT), i(i) {}
  bool operator==(const Arg r) const;
  json toJson();
};

struct ArgString : Arg {
  string str;
  ArgString(string str) : Arg(ASTRING), str(str) {}
  bool operator==(const Arg r) const;
  json toJson();
};

struct ArgType : Arg {
  Type* t;
  ArgType(Type* t) : Arg(ATYPE), t(t) {}
  bool operator==(const Arg r) const;
  json toJson();
};


//class Instantiable;
//struct ArgInst : Arg {
//  Instantiable* i;
//  ArgInst(Instantiable* i) : Arg(GINST), i(i) {}
//};

bool checkParams(Args args, Params params);

//bool operator==(const Args& l, const Args& r) {
//    if (l.size() != r.size()) return false;
//    for (auto field : args) {
//      auto rfield = r.args.find(field.first);
//      if(rfield == r.args.end()) return false;
//      if (!ArgEq(field.second,rfield->second)) return false;
//    }
//    return true;
//  }
//};

}//CoreIR namespace


//namespace std {
//  template<>
//  struct hash<CoreIR::Args> {
//    size_t operator() (const CoreIR::Args& p) const;
//  };
//}



#endif //GENARGS_HPP_
