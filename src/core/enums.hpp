#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>
#include <iostream>
#include <vector>

using namespace std;

typedef uint32_t uint;

typedef enum {BITIN, BITOUT,ARRAY,RECORD,ANY,TYPEGEN} TypeKind;
typedef enum {IFACE,INST,SEL} WireableKind;
typedef enum {MOD,GEN} InstantiableKind;
typedef enum {GSTRING,GINT,GTYPE} ArgKind;
typedef enum {VERILOG,SIMULATOR} MetadataKind;

typedef vector<ArgKind> ArgKinds;

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
string wireableKind2Str(WireableKind wb);

class Wire;
class Wireable;
class TypedWire;
TypedWire* castTypedWire(Wire* w);
//Type* wireable2Type(Wireable* w);

template <typename T>
T safecast(void* obj,string err="Cannot cast!");



#endif //ENUMS_HPP_
