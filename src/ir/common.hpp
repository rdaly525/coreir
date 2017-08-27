#ifndef COMMON_HPP_
#define COMMON_HPP_


#include <stdint.h>
#include <vector>
#include <deque>
#include <unordered_map>
#include <unordered_set>
#include <cassert>
#include <sstream>

using namespace std;


#define ASSERT(C,MSG) \
  if (!(C)) { \
    std::cout << "ERROR: " << MSG << endl << endl; \
    assert(C); \
  }


typedef uint32_t uint;
namespace CoreIR {

typedef enum {AINT=0,ASTRING=1,ATYPE=2,ABOOL=3} Param;

//other
class Namespace;
class Context;
struct Error;
class Arg;
class ArgInt;
class ArgString;
class ArgType;
class ArgBool;
typedef unordered_map<string,Param> Params;
typedef unordered_map<string,Arg*> Args;


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

class Type;
class BitType;
class BitInType;
class ArrayType;
class RecordType;
class NamedType;
class TypeGen;
typedef Type* (*TypeGenFun)(Context* c, Args args);
typedef vector<myPair<string,Type*>> RecordParams ;
typedef std::string (*NameGen_t)(Args);
typedef myPair<uint,Type*> ArrayParams ;
class TypeCache;
class MetaData;

//instantiable.hpp
class Instantiable;
class Generator;
class Module;
class ModuleDef;
typedef void (*ModuleDefGenFun)(ModuleDef*,Context*, Type*, Args);

class SelCache;
class Wireable;
class Interface;
class Instance;
class Select;

//typedef deque<string> SelectPath;

typedef deque<std::string> SelectPath;
typedef vector<std::reference_wrapper<const string>> ConstSelectPath;
typedef myPair<Wireable*,Wireable*> Connection;
//This is meant to be in relation to an instance. First wireable of the pair is of that instance.
typedef vector<std::pair<Wireable*,Wireable*>> LocalConnections;

class ConnectionComp {
  public:
    static bool SPComp(const SelectPath& l, const SelectPath& r);
    bool operator() (const Connection& l, const Connection& r);
};

//TODO Ugly hack to create a sorted connection. Should make my own connection class
Connection connectionCtor(Wireable* a, Wireable* b);


//TODO This stuff is super fragile. 
// Magic hash function I found online
template <class T> 
inline void hash_combine(size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

//These are defined in helpers
bool isNumber(string s);
bool isPower2(uint n);
string Param2Str(Param);
string Params2Str(Params);
string Args2Str(Args);
string SelectPath2Str(SelectPath path);
string Connection2Str(Connection con);
Param Str2Param(string s);

//Will call assertions
void checkArgsAreParams(Args args, Params params);

bool hasChar(const std::string s, char c);


template<class T> std::string toString(const T& t) {
  ostringstream stream;
  stream << t;
  return stream.str();
}

template<typename BackInserter>
BackInserter splitString(const std::string &s, char delim) {
    BackInserter elems;
    stringstream ss;
    ss.str(s);
    string item;
    while (std::getline(ss, item, delim)) {
      elems.push_back(item);
    }
    return elems;
}
template <class T, class A>
T join(const A &begin, const A &end, const T &t) {
  T result;
  for (A it=begin; it!=end; it++) {
    if (!result.empty())
      result.append(t);
    result.append(*it);
  }
  return result;
}

vector<string> splitRef(string s);

//template<typename container>
//std::string joinString(const container arr, std::string del);

static unordered_map<std::string,unordered_set<std::string>> opmap({
  {"unary",{"not","neg"}},
  {"unaryReduce",{"andr","orr","xorr"}},
  {"binary",{
    "and","or","xor",
    "dshl","dlshr","dashr",
    "add","sub","mul",
    "udiv","urem",
    "sdiv","srem","smod"
  }},
  {"binaryReduce",{"eq",
    "slt","sgt","sle","sge",
    "ult","ugt","ule","uge"
  }},
  {"ternary",{"mux"}},
});


} //CoreIR namespace

namespace std {
  //slow
  template <class T1, class T2>
  struct hash<CoreIR::myPair<T1,T2>> {
    //template <class T1, class T2>
    size_t operator() (const CoreIR::myPair<T1,T2>& p) const {
      auto h1 = std::hash<T1>{}(p.first);
      auto h2 = std::hash<T2>{}(p.second);
      return h1 ^ (h2*3);
    }
  };

  template <>
  struct hash<CoreIR::Args> {
    size_t operator() (const CoreIR::Args& args) const;
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

#endif //COMMON_HPP_
