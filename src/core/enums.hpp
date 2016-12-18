#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>
#include <iostream>

using namespace std;

typedef uint32_t uint;

typedef enum {IN,OUT} Dir;
typedef enum {INT,ARRAY,RECORD} TypeEnum;
typedef enum {IFACE,INST,SEL,TIFACE,TINST,TSEL} WireableEnum;
typedef enum {MDEF,MDEC,GDEC,GDEF,TMDEF} InstantiableEnum;
typedef enum {GSTRING,GINT,GMOD} genargEnum;

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
string TypeEnum2Str(TypeEnum t);
string wireableEnum2Str(WireableEnum wb);

class Type;
class Wire;
class Wireable;
class TypedWire;
TypedWire* castTypedWire(Wire* w);
Type* wireable2Type(Wireable* w);
Dir flipDir(Dir d);
#endif //ENUMS_HPP_
