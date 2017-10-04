#ifndef COREIR_FWD_DECLARE_HPP_
#define COREIR_FWD_DECLARE_HPP_

#include <stdint.h>
#include <vector>
#include <deque>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <cassert>
#include <sstream>
#include <iostream>

#define ASSERT(C,MSG) \
  if (!(C)) { \
    std::cout << "ERROR: " << MSG << std::endl << std::endl; \
    assert(C); \
  }

typedef uint32_t uint;

namespace bsim {
  class dynamic_bit_vector;
}
typedef bsim::dynamic_bit_vector BitVector;

namespace CoreIR {

class Context;
struct Error;
class Namespace;
class RefName;

class DirectedConnection;
class DirectedInstance;
class DirectedModule;

//Types : types.h
class Type;
class BitType;
class BitInType;
class ArrayType;
class RecordType;
class NamedType;

class TypeGen;

class TypeCache;
class ValueCache;

//value.h
class Value;
class Arg;
class Const;

template<class T>
class TemplatedConst;

typedef TemplatedConst<bool> ConstBool;
typedef TemplatedConst<int> ConstInt;
typedef TemplatedConst<BitVector> ConstBitVector;
typedef TemplatedConst<std::string> ConstString;
typedef TemplatedConst<Type*> ConstCoreIRType;



//valuetype.h
class ValueType;
class BoolType;
class IntType;
class BitVectorType;
class StringType;
class CoreIRType;


class MetaData;

//instantiable.h
class Instantiable;
class Generator;
class Module;

class ModuleDef;
class GeneratorDef;

class Wireable;
class Interface;
class Instance;
class Select;

class Pass;
class PassManager;

typedef std::map<std::string,Value*> Values;
typedef std::map<std::string,ValueType*> Params;

bool operator==(const Values& l, const Values& r);


//Function prototypes for APIs
typedef std::function<Type*(Context* c, Values genargs)> TypeGenFun;
typedef std::string (*NameGenFun)(Values);
typedef std::function<std::pair<Params,Values>(Context*,Values)> ModParamsGenFun;
typedef void (*ModuleDefGenFun)(Context* c,Values genargs,ModuleDef*);

typedef std::vector<std::pair<std::string,Type*>> RecordParams ;

typedef std::deque<std::string> SelectPath;
typedef std::vector<std::reference_wrapper<const std::string>> ConstSelectPath;
typedef std::pair<Wireable*,Wireable*> Connection;
//This is meant to be in relation to an instance. First wireable of the pair is of that instance.
typedef std::vector<std::pair<Wireable*,Wireable*>> LocalConnections;

//TODO This stuff is super fragile. 
// Magic hash function I found online
template <class T> 
inline void hash_combine(size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}



} //CoreIR namespace

namespace std {
  ////slow
  //template <class T1, class T2>
  //struct hash<CoreIR::myPair<T1,T2>> {
  //  //template <class T1, class T2>
  //  size_t operator() (const CoreIR::myPair<T1,T2>& p) const {
  //    auto h1 = std::hash<T1>{}(p.first);
  //    auto h2 = std::hash<T2>{}(p.second);
  //    return h1 ^ (h2<<1);
  //  }
  //};

  template <>
  struct hash<CoreIR::Values> {
    size_t operator() (const CoreIR::Values& args) const;
  };
  
  template <>
  struct hash<CoreIR::SelectPath> {
    size_t operator() (const CoreIR::SelectPath& path) const {
      size_t h = 0;
      for (auto str : path) {
        CoreIR::hash_combine(h,str);
      }
      return h;
    }
  };

}

#endif 
