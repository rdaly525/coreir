#ifndef GENARGS_HPP_
#define GENARGS_HPP_

#include "enums.hpp"
//genargsType(type* ts)
//genType = string
//        | int
//        | ModuleDef

struct GenArg {
  virtual ~GenArg() {}
  genargKind kind;
  GenArg(genargKind kind) : kind(kind) {}
};

struct GenString : GenArg {
  string str;
  GenString(string str) : GenArg(GSTRING), str(str) {}
};

struct GenInt : GenArg {
  int i;
  GenInt(int i) : GenArg(GINT), i(i) {}
};

class ModuleDef;
struct GenMod : GenArg {
  ModuleDef* mod;
  GenMod(ModuleDef* mod) : GenArg(GMOD), mod(mod) {}
};

typedef vector<genargKind> genargs_t;
struct GenArgs {
  genargs_t argtypes;
  vector<GenArg*> args;
  GenArgs(genargs_t argtypes) : argtypes(argtypes) {}
  GenArgs(genargs_t argtypes, vector<void*> _args) : argtypes(argtypes) {
    setArgs(_args);
  }
  ~GenArgs() {
    for (auto arg : args) delete arg;
  }
  void setArgs(vector<void*> _args) {
    assert(_args.size()==argtypes.size());
    for (uint i=0; i<argtypes.size(); ++i) {
      switch(argtypes[i]) {
        case(GSTRING) : {
          string* s = safecast<string*>(_args[i],"Bad Type!");
          args.push_back(new GenString(*s));
        }
        case(GINT) : {
          int* i = safecast<int*>(_args[i]);
          args.push_back(new GenInt(*i));
        }
        case(GMOD) : {
          ModuleDef* m = safecast<ModuleDef*>(_args[i]);
          args.push_back(new GenMod(m));
        }
      }
    }
  }
  GenArg* operator[](const int i) {
    return args[i];
  }
};


#endif //GENARGS_HPP_
