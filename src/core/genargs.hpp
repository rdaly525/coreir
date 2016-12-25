#ifndef GENARGS_HPP_
#define GENARGS_HPP_

#include "enums.hpp"
//genargsType(type* ts)
//genType = string
//        | int
//        | ModuleDef

struct GenArg {
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

//Probably should add in the ability to pass in a type

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
    for (uint i=0; i<argtypes.size(); ++i) {
      switch(argtypes[i]) {
        case(GSTRING) : args.push_back(new GenString(*(string*)(_args[i])));
        case(GINT) : args.push_back(new GenInt(*(int*)(_args[i])));
        case(GMOD) : args.push_back(new GenMod((ModuleDef*) (_args[i])));
      }
    }
  }
  GenArg* operator[](const int i) {
    return args[i];
  }
};


#endif //GENARGS_HPP_
