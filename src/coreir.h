//This is for the C API
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t u32;

typedef struct COREContext COREContext;
typedef struct CORENamespace CORENamespace;
typedef struct COREType COREType;
typedef struct COREModule COREModule;
typedef struct COREModuleDef COREModuleDef;
typedef struct CORERecordParam CORERecordParam;
typedef struct COREInstance COREInstance;
typedef struct COREInterface COREInterface;
typedef struct CORESelect CORESelect;
typedef struct COREWireable COREWireable;
typedef struct COREGenParams COREGenParams;
typedef struct COREGenArgs COREGenArgs;
typedef struct COREGenArg COREGenArg;

typedef enum {COREGSTRING,COREGINT,COREGTYPE} COREGenParam;


//Context COREreater/deleters
extern COREContext* CORENewContext();
extern void COREDeleteContext(COREContext*);

//Type COREonstructors
extern COREType* COREAny(COREContext* CORE);
extern COREType* COREBitIn(COREContext* CORE);
extern COREType* COREBitOut(COREContext* CORE);
extern COREType* COREArray(COREContext* CORE, u32 len, COREType* elemType);

//Record Params
extern CORERecordParam* CORENewRecordParam(COREContext* c);
//Check Errors
extern void CORERecordParamAddField(CORERecordParam* record_param, char* name, COREType* type);
extern COREType* CORERecord(COREContext* c, CORERecordParam* record_param);

//Create GenParams
extern COREGenParams* CORENewGenParams(COREContext* c);
extern void COREGenParamsAddField(COREGenParams* genparams, char* name, COREGenParam genparam);

//Create GenArgs
extern COREGenArgs* CORENewGenArgs(COREContext* c);
extern void COREGenArgsAddField(COREGenArgs* genargs, char* name, COREGenArg* genarg);

//Create specific GenArg
extern COREGenArg* COREGInt(COREContext* c,int i);


extern void COREPrintType(COREType* t);

//Errors:
extern COREModule* CORELoadModule(COREContext* c, char* filename, bool* err);

//Errors:
//  Cannot open file for writing
extern void CORESaveModule(COREModule* module, char* filename, bool* err);

extern CORENamespace* COREGetGlobal(COREContext* c);

//Errors:
//  Invalid arg: Module name already exists
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, COREGenParams* configparams);


extern void COREPrintModule(COREModule* m);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
void COREModuleAddDef(COREModule* module, COREModuleDef* module_def);

//Errors:
//  Invalid arg: instance name already exists
extern COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, COREGenArgs* config);
extern COREInterface* COREModuleDefGetInterface(COREModuleDef* m);

//Errors:
//  Wire Error;
//  Typechecking errors
extern void COREModuleDefWire(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern CORESelect* COREInstanceSelect(COREInstance* instance, char* field);
extern CORESelect* COREInterfaceSelect(COREInterface* interface, char* field);


extern void COREPrintErrors(COREContext* c);
/*
//Module stuff
extern COREType* COREModuleGetType(COREModule* m);
extern int COREModuleHasDef(COREModule* m);
extern COREModuleDef* COREModuleGetDef(COREModule* m);

// ModuleDef stuff
extern COREInstance** COREGetInstances(COREModuleDef* m, uint* numInstances);
extern COREWireablePair* COREGetWires(COREModuleDef* m, uint* numWires);

//Wireable stuff
extern COREWireable** COREGetConnections(COREWireable* w, uint* numConnections);
extern COREStr2WireableMap* COREGetChildren(Wireable* w);

typedef struct COREWireableSet COREWireableSet;

//Maybe macrofy these
typedef struct {
  COREWireable* first;
  COREWireable* second;
} COREWireablePair;

typedef struct COREStr2WireableMap;
extern COREWireable* COREStr2WireableMapGet(COREStr2WireableMap* m, char* key);


extern COREWireableSet* CORENewWireableSet();
extern COREWireableSet* 


*/
