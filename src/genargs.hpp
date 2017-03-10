#ifndef GENARGS_HPP_
#define GENARGS_HPP_


#include "types.hpp"
#include "common.hpp"
#include <cassert>
//#include <unordered_map>

using namespace std;

//struct ArgKinds {
//  unordered_map<string,ArgKind> dict;
//  ArgKinds(unordered_map<string,ArgKind> dict) : dict(dict) {}
//  ArgKind operator[](const string& key) {
//    //What should I do if this is not valid?
//    return dict[key];
//  }
//}

struct GenArg {
  virtual ~GenArg() {}
  ArgKind kind;
  GenArg(ArgKind kind) : kind(kind) {}
  bool isKind(ArgKind k) { return kind==k; }
};

struct GenString : GenArg {
  string str;
  GenString(string str) : GenArg(GSTRING), str(str) {}
};

struct GenInt : GenArg {
  int i;
  GenInt(int i) : GenArg(GINT), i(i) {}
};

struct GenType : GenArg {
  Type* t;
  GenType(Type* t) : GenArg(GTYPE), t(t) {}
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

  GenArg* operator[](const string s) const;
  bool GenArgEq(GenArg* a, GenArg* b);

  bool checkKinds(ArgKinds kinds) {
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
