#ifndef GENARGS_HPP_
#define GENARGS_HPP_


#include "types.hpp"
#include "common.hpp"
#include <cassert>
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

//struct GenParams {
//  unordered_map<string,GenParam> dict;
//  GenParams(unordered_map<string,GenParam> dict) : dict(dict) {}
//  GenParam operator[](const string& key) {
//    //What should I do if this is not valid?
//    return dict[key];
//  }
//}

struct GenArg {
  virtual ~GenArg() {}
  GenParam kind;
  GenArg(GenParam kind) : kind(kind) {}
  bool isKind(GenParam k) { return kind==k; }
  virtual json toJson()=0;
};

struct GenString : GenArg {
  string str;
  GenString(string str) : GenArg(GSTRING), str(str) {}
  json toJson();
};

struct GenInt : GenArg {
  int i;
  GenInt(int i) : GenArg(GINT), i(i) {}
  json toJson();
};

struct GenType : GenArg {
  Type* t;
  GenType(Type* t) : GenArg(GTYPE), t(t) {}
  json toJson();
};


//class Instantiable;
//struct GenInst : GenArg {
//  Instantiable* i;
//  GenInst(Instantiable* i) : GenArg(GINST), i(i) {}
//};
namespace std {
  template<>
  struct hash<GenArgs> {
    size_t operator() (const GenArgs& p) const;
  };
}

struct GenArgs {
  Context* c;
  unordered_map<string,GenArg*> args;
  GenArgs(Context* c, unordered_map<string,GenArg*> args) : c(c), args(args) {}
  void addField(string s, GenArg* arg) { args[s] = arg;}
  json toJson();
  GenArg* operator[](const string s) const;
  void print() {
    for (auto arg : args) cout << " Arg: " << arg.first << endl;
  }
  bool GenArgEq(GenArg* a, GenArg* b);

  bool checkParams(GenParams kinds) {
    if (args.size() != kinds.size()) return false;
    for (auto field : args) {
      auto kind = kinds.find(field.first);
      if (kind == kinds.end()) return false;
      assert(kind->first == field.first);
      if (! field.second->isKind(kind->second) ) return false;
    }
    return true;
  }
  bool operator==(const GenArgs r) {
    if (args.size() != r.args.size()) return false;
    for (auto field : args) {
      auto rfield = r.args.find(field.first);
      if(rfield == r.args.end()) return false;
      if (!GenArgEq(field.second,rfield->second)) return false;
    }
    return true;
  }
  bool operator!=(GenArgs r) {
    return !(*this == r);
  }
};


#endif //GENARGS_HPP_
