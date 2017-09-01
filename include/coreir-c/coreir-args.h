//This needs to stay the same as CoreIR::Param
typedef enum {
  COREIntParam = 0,
  COREStringParam = 1,
  CORETypeParam = 2,
  COREBoolParam = 3
} COREParam;


//Get the Type Kind enum
extern COREParam COREGetArgKind(COREArg* arg);

//Create Args
extern COREArg* COREArgInt(COREContext* c,int i);
extern COREArg* COREArgString(COREContext* c,char* str);

//Arg Getter functions will assert on wrong arg type
extern int COREArgIntGet(COREArg* a);
extern const char* COREArgStringGet(COREArg* a);
extern bool COREArgBoolGet(COREArg* a);
