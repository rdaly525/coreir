#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>
#include <iostream>

using namespace std;

typedef uint32_t uint;

typedef enum {IN,OUT} Dir;
typedef enum {BIT,ARRAY,RECORD,TDEF,TGDEF} TypeKind;
typedef enum {IFACE,INST,SEL,TIFACE,TINST,TSEL} WireableKind;
typedef enum {MDEF,MDEC,GDEC,GDEF,TMDEF} InstantiableKind;
typedef enum {GSTRING,GINT,GMOD} genargKind;
typedef enum {VERILOG,SIMULATOR} MetadataKind;

struct GenArgs;
struct simfunctions_t {
  //void* iface,void* state,void* dirty,void* genargs)
  void (*updateOutput)(void*,void*,void*,GenArgs*);
  void* (*allocateState)(void);
  void (*updateState)(void*,void*,void*,GenArgs*);
  void (*deallocateState)(void*);
};



//These are defined in helpers
bool isNumber(string s);
string TypeKind2Str(TypeKind t);
string wireableKind2Str(WireableKind wb);

class Type;
class Wire;
class Wireable;
class TypedWire;
TypedWire* castTypedWire(Wire* w);
Type* wireable2Type(Wireable* w);
Dir flipDir(Dir d);

template <typename T>
T safecast(void* obj,string err="Cannot cast!");



#endif //ENUMS_HPP_
