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
  virtual bool operator==(const Arg& r) const {
    return r.isKind(kind);
  }
  friend bool operator==(const Args& l, const Args& r);
};

struct ArgInt : Arg {
  int i;
  ArgInt(int i) : Arg(AINT), i(i) {}
  bool operator==(const Arg& r) const;
  json toJson();
};

struct ArgString : Arg {
  string str;
  ArgString(string str) : Arg(ASTRING), str(str) {}
  bool operator==(const Arg& r) const;
  json toJson();
};

struct ArgType : Arg {
  Type* t;
  ArgType(Type* t) : Arg(ATYPE), t(t) {}
  bool operator==(const Arg& r) const;
  json toJson();
};

//class Instantiable;
//struct ArgInst : Arg {
//  Instantiable* i;
//  ArgInst(Instantiable* i) : Arg(AINST), i(i) {}
//};


bool checkParams(Args args, Params params);

}//CoreIR namespace


#endif //GENARGS_HPP_
