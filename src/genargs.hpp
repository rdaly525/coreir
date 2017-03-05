#ifndef GENARGS_HPP_
#define GENARGS_HPP_

#include "types.hpp"
#include "common.hpp"
#include <cassert>

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

template<>
struct hash<GenArgs> {
  size_t operator() (const GenArgs& p) const;
};

struct GenArgs {
  uint len;
  vector<GenArg*> args;
  GenArgs(uint len, vector<GenArg*> _args) : len(len), args(_args) {
    assert(len < 10);
    assert(len == args.size() );
  }
  GenArg* operator[](const int i) const {
    return args[i];
  }
  bool GenArgEq(GenArg* a, GenArg* b);

  bool checkKinds(ArgKinds kinds) {
    if (len != kinds.size()) return false;
    bool good = true;
    for (uint i=0; i<len; ++i) {
      good &= args[i]->isKind(kinds[i]);
    }
    return good;
  }
  bool operator==(GenArgs r) {
    if (len != r.len) return false;
    bool good = true;
    for (uint i=0; i<len; i++) {
      good &= GenArgEq(args[i],r[i]);
    }
    return good;
  }
  bool operator!=(GenArgs r) {
    return !(*this == r);
  }
};


#endif //GENARGS_HPP_
