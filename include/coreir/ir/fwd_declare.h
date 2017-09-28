#ifndef COREIR_FWD_DECLARE_HPP_
#define COREIR_FWD_DECLARE_HPP_

#include <stdint.h>
#include <vector>
#include <deque>
#include <map>
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

namespace CoreIR {

class Context;
struct Error;
class Namespace;

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

//value.h
class Value;
class Arg;
class Const;

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

namespace bsim {
  class dynamic_bit_vector;
}
typedef bsim::dynamic_bit_vector bit_vector;


typedef std::shared_ptr<Value> ValuePtr;
typedef std::shared_ptr<Arg> ArgPtr;
typedef std::shared_ptr<Const> ConstPtr;
typedef std::map<std::string,ConstPtr> Consts;
typedef std::map<std::string,ValuePtr> Values;
typedef std::map<std::string,Arg*> Args;

typedef std::map<std::string,ValueType*> Params;

bool operator==(const Values& l, const Values& r);

//TODO this is a hack solution that should be fixed
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

typedef std::vector<myPair<std::string,Type*>> RecordParams ;
typedef myPair<uint,Type*> ArrayParams ;

typedef std::deque<std::string> SelectPath;
typedef std::vector<std::reference_wrapper<const std::string>> ConstSelectPath;
typedef myPair<Wireable*,Wireable*> Connection;
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
  struct hash<CoreIR::Values> {
    size_t operator() (const CoreIR::Values& args) const;
  };
  
  template <>
  struct hash<CoreIR::SelectPath> {
    size_t operator() (const CoreIR::SelectPath& path) const {
      size_t h = 0;
      for (auto str : path) {
        auto hstr = std::hash<std::string>{}(str);
        h = (h<<1) ^ hstr;
      }
      return h;
    }
  };

}

#endif 
