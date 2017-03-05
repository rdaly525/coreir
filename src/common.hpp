#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>
#include <iostream>
#include <vector>
#include <unordered_map>

using namespace std;

typedef uint32_t uint;

typedef enum {BITIN, BITOUT,ARRAY,RECORD,ANY,TYPEGEN} TypeKind;
typedef enum {GSTRING,GINT,GTYPE} ArgKind;

typedef enum {MOD,GEN} InstantiableKind;
typedef enum {IFACE,INST,SEL} WireableKind;

//other
class Namespace;
class CoreIRContext;
struct GenArg;
struct GenInt;
struct GenString;
struct GenType;
struct GenArgs;
typedef vector<ArgKind> ArgKinds;

//Types.hpp
class Type;
typedef Type* (*TypeGenFun)(CoreIRContext* c, GenArgs* args, ArgKinds argkinds);
struct TypeGen;
typedef vector<std::pair<string,Type*>> RecordParams ;
class TypeCache;

//instantiable.hpp
class Instantiable;
class Module;
class ModuleDef;
class Generator;
typedef Module* (*genFun)(CoreIRContext*,Type*,GenArgs*,ArgKinds);

class Wireable;
class SelCache;
class Wireable;
class Interface;
class Instance;
class Select;


// Magic hash function I found online
template <class T> 
inline void hash_combine(size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

//slow
template <class T1, class T2>
struct hash<std::pair<T1,T2>> {
  //template <class T1, class T2>
  size_t operator() (const std::pair<T1,T2>& p) const {
    auto h1 = std::hash<T1>{}(p.first);
    auto h2 = std::hash<T2>{}(p.second);
    return h1 ^ h2;
  }
};

//struct simfunctions_t {
//  //void* iface,void* state,void* dirty,void* genargs)
//  void (*updateOutput)(void*,void*,void*,GenArgs*);
//  void* (*allocateState)(void);
//  void (*updateState)(void*,void*,void*,GenArgs*);
//  void (*deallocateState)(void*);
//};



//These are defined in helpers
bool isNumber(string s);
string TypeKind2Str(TypeKind t);
string ArgKind2Str(ArgKind);
string ArgKinds2Str(ArgKinds);
string wireableKind2Str(WireableKind wb);




//TypedWire* castTypedWire(Wire* w);
//Type* wireable2Type(Wireable* w);

//template <typename T>
//T safecast(void* obj,string err="Cannot cast!");



#endif //ENUMS_HPP_
