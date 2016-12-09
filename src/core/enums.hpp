#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>
#include <iostream>
using namespace std;

typedef uint32_t uint;

typedef enum {INT,ARRAY,RECORD} TypeEnum;
typedef enum {IN,OUT} Dir;
typedef enum {IFACE,INST,SEL,TIFACE,TINST,TSEL} WireableEnum;
typedef enum {MDEF,MDEC,GDEC,GDEF,TMDEF} InstantiableEnum;


struct Genargs;
struct simfunctions_t {
  //void* iface,void* state,void* dirty,void* genargs)
  void (*updateOutput)(void*,void*,void*,Genargs*);
  void* (*allocateState)(void);
  void (*updateState)(void*,void*,void*,Genargs*);
  void (*deallocateState)(void*);
};



//These are defined in helpers
bool isNumber(string s);
string wireableEnum2Str(WireableEnum wb);



#endif //ENUMS_HPP_
