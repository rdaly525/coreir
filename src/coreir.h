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
typedef struct COREParams COREParams;
typedef struct COREArgs COREArgs;
typedef struct COREArg COREArg;

typedef struct COREConnection COREConnection;
typedef struct COREWirePath COREWirePath;


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

//Create Params
extern COREParams* CORENewParams(COREContext* c);
extern void COREParamsAddField(COREParams* genparams, char* name, int genparam);

//Create Args
extern COREArgs* CORENewArgs(COREContext* c);
extern void COREArgsAddField(COREArgs* genargs, char* name, COREArg* genarg);

//Create specific Arg
extern COREArg* COREGInt(COREContext* c,int i);


extern void COREPrintType(COREType* t);

//Errors:
extern COREModule* CORELoadModule(COREContext* c, char* filename, bool* err);

//Errors:
//  Cannot open file for writing
extern void CORESaveModule(COREModule* module, char* filename, bool* err);

extern CORENamespace* COREGetGlobal(COREContext* c);

//Errors:
//  Invalid arg: Module name already exists
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, COREParams* configparams);


extern void COREPrintModule(COREModule* m);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
extern COREModuleDef* COREModuleGetDefs(COREModule* m);
void COREModuleAddDef(COREModule* module, COREModuleDef* module_def);

//Errors:
//  Invalid arg: instance name already exists
extern COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, COREArgs* config);
extern COREInterface* COREModuleDefGetInterface(COREModuleDef* m);

//Errors:
//  Wire Error;
//  Typechecking errors
extern void COREModuleDefWire(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern CORESelect* COREInstanceSelect(COREInstance* instance, char* field);
extern CORESelect* COREInterfaceSelect(COREInterface* interface, char* field);
extern COREInstance** COREModuleDefGetInstances(COREModuleDef* m, int* numInstances);
// extern COREConnection* COREModuleDefGetConnections(COREModuleDef* m, int* numWires);
extern COREWireable* COREConnectionGetFirst(COREConnection* connection);
extern COREWireable* COREConnectionGetSecond(COREConnection* connection);
extern COREWireable** COREWireableGetConnectedWireables(COREWireable* wireable, int* numWireables);
extern CORESelect* COREWireableSelect(COREWireable* w, char* name);
extern COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name);
// extern COREWirePath* COREWireableGetWirePath(COREWireable* w);

extern void COREPrintErrors(COREContext* c);
