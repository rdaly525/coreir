#ifndef ENUMS_HPP_
#define ENUMS_HPP_

#include <stdint.h>
#include <iostream>
#include <vector>
#include <unordered_map>

using namespace std;

typedef uint32_t uint;
namespace CoreIR {

typedef enum {BITIN, BITOUT,ARRAY,RECORD,ANY,TYPEGEN} TypeKind;
typedef enum {AINT=0,ASTRING=1,ATYPE=2} Param;

typedef enum {MOD,GEN} InstantiableKind;
typedef enum {IFACE,INST,SEL} WireableKind;

//other
class Namespace;
class Context;
struct Error;
struct Arg;
struct ArgInt;
struct ArgString;
struct ArgType;
typedef unordered_map<string,Param> Params;
typedef unordered_map<string,Arg*> Args;


// This is so I do not overload the std::hash<std::pair<T1,T2>> class.
// Use myPair for hashing
template<class T1, class T2>
struct myPair {
  T1 first;
  T2 second;
  myPair(T1 first, T2 second) : first(first), second(second) {}
  friend bool operator==(const myPair& l,const myPair& r) {
    return l.first==r.first && l.second==r.second;
  }
};

class Type;
class Module;
typedef Type* (*TypeGenFun)(Context* c, Args args, Params genparams);
struct TypeGen;
typedef vector<myPair<string,Type*>> RecordParams ;
typedef myPair<uint,Type*> ArrayParams ;
class TypeCache;
struct Metadata;


//instantiable.hpp
class Instantiable;
class ModuleDef;
class Generator;
typedef Module* (*genFun)(Context*,Type*,Args,Params);

class Wireable;
class SelCache;
class Wireable;
class Interface;
class Instance;
class Select;

typedef std::pair<string,vector<string>> WirePath;
struct Connection;




//TODO This stuff is super fragile. 
// Magic hash function I found online
template <class T> 
inline void hash_combine(size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

//These are defined in helpers
bool isNumber(string s);
string TypeKind2Str(TypeKind t);
string Param2Str(Param);
string Params2Str(Params);
string wireableKind2Str(WireableKind wb);
Param Str2Param(string s);



} //CoreIR namespace

namespace std {
  //slow
  template <class T1, class T2>
  struct hash<CoreIR::myPair<T1,T2>> {
    //template <class T1, class T2>
    size_t operator() (const CoreIR::myPair<T1,T2>& p) const {
      auto h1 = std::hash<T1>{}(p.first);
      auto h2 = std::hash<T2>{}(p.second);
      return h1 ^ (h2<<1);
    }
  };

  template <>
  struct hash<CoreIR::Args> {
    size_t operator() (const CoreIR::Args& args) const;
  };

}


//TypedWire* castTypedWire(Wire* w);
//Type* wireable2Type(Wireable* w);

//template <typename T>
//T safecast(void* obj,string err="Cannot cast!");



#endif //ENUMS_HPP_
