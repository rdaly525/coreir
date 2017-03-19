//This is for the C API
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t u32;

typedef struct COREContext COREContext;
typedef struct CORENamespace CORENamespace;
typedef struct COREType COREType;
typedef struct COREModule COREModule;
typedef struct COREModuleDef COREModuleDef;
typedef struct COREInstance COREInstance;
typedef struct COREInterface COREInterface;
typedef struct CORESelect CORESelect;
typedef struct COREWireable COREWireable;
typedef struct COREArg COREArg;

typedef enum {
    STR2TYPE_MAP = 0,
    STR2ARG_MAP = 1,
    STR2PARAM_MAP = 2
} COREContainerKind;

//keys and values will be freed
void* CORENewMap(COREContext* c, void* keys, void* values, u32 len, COREMapKind kind);
//void* COREMapAt(void* container,void* key,COREContainerKind kind, bool* err);

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
extern COREType* CORERecord(COREContext* c, void* recordparams);


////Record Params
//extern CORERecordParam* CORENewRecordParam(COREContext* c);
////Check Errors
//extern void CORERecordParamAddField(CORERecordParam* record_param, char* name, COREType* type);

////Create Params
//extern COREParams* CORENewParams(COREContext* c);
//extern void COREParamsAddField(COREParams* genparams, char* name, int genparam);

////Create Args
extern COREArgs* CORENewArgs(COREContext* c,void* args);

//Create specific Arg
extern const char* COREArg2Str(COREArg* a);
extern COREArg* COREInt2Arg(COREContext* c,int i);

extern void COREPrintType(COREType* t);

//Errors:
extern COREModule* CORELoadModule(COREContext* c, char* filename, bool* err);

//Errors:
//  Cannot open file for writing
extern void CORESaveModule(COREModule* module, char* filename, bool* err);

extern CORENamespace* COREGetGlobal(COREContext* c);


extern const char* COREGetInstRefName(COREInstance* iref);

//Errors:
//  Invalid arg: Module name already exists
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, void* configparams);


extern void COREPrintModule(COREModule* m);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
extern COREModuleDef* COREModuleGetDefs(COREModule* m);
void COREModuleAddDef(COREModule* module, COREModuleDef* module_def);

//Errors:
//  Invalid arg: instance name already exists
extern COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, void* config); //config will be Args*
extern COREInterface* COREModuleDefGetInterface(COREModuleDef* m);
extern COREArg* COREGetConfigValue(COREInstance* i, char* s); 

//Errors:
//  Wire Error;
//  Typechecking errors
extern void COREModuleDefWire(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern CORESelect* COREInstanceSelect(COREInstance* instance, char* field);
extern CORESelect* COREInterfaceSelect(COREInterface* interface, char* field);
extern COREInstance** COREModuleDefGetInstances(COREModuleDef* m, u32* numInstances);
// extern COREConnection* COREModuleDefGetConnections(COREModuleDef* m, int* numWires);
extern COREWireable* COREConnectionGetFirst(COREConnection* connection);
extern COREWireable* COREConnectionGetSecond(COREConnection* connection);
extern COREWireable** COREWireableGetConnectedWireables(COREWireable* wireable, int* numWireables);
extern CORESelect* COREWireableSelect(COREWireable* w, char* name);
extern COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name);
extern COREModuleDef* COREWireableGetModuleDef(COREWireable* w);
extern COREModule* COREModuleDefGetModule(COREModuleDef* m);
extern const char** COREWireableGetAncestors(COREWireable* w, int* num_ancestors);

extern void COREPrintErrors(COREContext* c);
