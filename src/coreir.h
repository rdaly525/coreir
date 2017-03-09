//This is for the C API
#include "stdint.h"

typedef uint32_t u32;

typedef struct COREContext COREContext;
typedef struct COREType COREType;
typedef struct COREModule COREModule;
typedef struct COREModuleDef COREModuleDef;
typedef struct CORERecordParam CORERecordParam;



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

extern COREModule* CORELoadModule(COREContext* c, char* filename);
extern COREModule* CORENewModule(COREContext* context, char* name, COREType* type);
extern void COREPrintModule(COREModule* m);

/*
//Module stuff
extern COREType* COREModuleGetType(COREModule* m);
extern int COREModuleHasDef(COREModule* m);
extern COREModuleDef* COREModuleGetDef(COREModule* m);

// ModuleDef stuff
extern COREInterface* COREGetInterface(COREModuleDef* m);
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
