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
typedef struct COREWiring COREWiring;



//Context COREreater/deleters
extern COREContext* CORENewContext();
extern void COREDeleteContext(COREContext*);

//Type COREonstructors
extern COREType* COREAny(COREContext* CORE);
extern COREType* COREBitIn(COREContext* CORE);
extern COREType* COREBitOut(COREContext* CORE);
extern COREType* COREArray(COREContext* CORE, u32 len, COREType* elemType);

extern CORERecordParam* CORENewRecordParam(COREContext* context);
extern void CORERecordParamAddField(CORERecordParam* record_param, char* name, COREType* type);
extern COREType* CORERecord(COREContext* context, CORERecordParam* record_param);

extern void COREPrintType(COREType* t);

//err is a boolean flag 
extern COREModule* CORELoadModule(COREContext* c, char* filename, bool* err);
extern void CORESaveModule(COREModule* module, char* filename, bool* err);

extern CORENamespace* COREGetGlobal(COREContext* c);
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type);
extern void COREPrintModule(COREModule* m);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
extern COREInstance* COREModuleDefAddInstanceModule(COREModuleDef* module_def, char* name, COREModule* module);
extern COREInterface* COREModuleDefGetInterface(COREModuleDef* m);
extern void COREModuleDefWire(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern CORESelect* COREInstanceSelect(COREInstance* instance, char* field);
extern CORESelect* COREInterfaceSelect(COREInterface* interface, char* field);
extern COREInstance** COREModuleDefGetInstances(COREModuleDef* m, int* numInstances);
extern COREWiring* COREModuleDefGetWires(COREModuleDef* m, int* numWires);

/*
//Module stuff
extern COREType* COREModuleGetType(COREModule* m);
extern int COREModuleHasDef(COREModule* m);
extern COREModuleDef* COREModuleGetDef(COREModule* m);

// ModuleDef stuff

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
