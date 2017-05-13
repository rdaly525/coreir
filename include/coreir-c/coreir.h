#ifndef COREIR_C_H_
#define COREIR_C_H_

#include <stdint.h>
#include <stdbool.h>

#include "../coreir-c/ctypes.h" 

//keys and values will not be freed
void* CORENewMap(COREContext* c, void* keys, void* values, u32 len, COREMapKind kind);

//Context COREreater/deleters
extern COREContext* CORENewContext();
extern void COREDeleteContext(COREContext*);

//Type COREonstructors
extern COREType* COREAny(COREContext* CORE);
extern COREType* COREBitIn(COREContext* CORE);
extern COREType* COREBit(COREContext* CORE);
extern COREType* COREArray(COREContext* CORE, u32 len, COREType* elemType);
extern COREType* CORERecord(COREContext* c, void* recordparams);

//Create specific Arg
extern const char* COREArg2Str(COREArg* a, bool* err);
extern int COREArg2Int(COREArg* a, bool* err);
extern COREArg* COREInt2Arg(COREContext* c,int i);
extern COREArg* COREStr2Arg(COREContext* c,char* str);

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
extern COREDirectedModule* COREModuleNewDirectedModule(COREModule* module);

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
extern COREConnection** COREModuleDefGetConnections(COREModuleDef* m, int* numWires);
extern COREWireable* COREConnectionGetFirst(COREConnection* c);
extern COREWireable* COREConnectionGetSecond(COREConnection* c);
extern COREWireable** COREWireableGetConnectedWireables(COREWireable* wireable, int* numWireables);
extern CORESelect* COREWireableSelect(COREWireable* w, char* name);
extern COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name);
extern COREModuleDef* COREWireableGetModuleDef(COREWireable* w);
extern COREModule* COREModuleDefGetModule(COREModuleDef* m);
extern const char** COREWireableGetAncestors(COREWireable* w, int* num_ancestors);
extern void COREPrintErrors(COREContext* c);
extern const char* CORENamespaceGetName(CORENamespace* n);

// BEGIN : directedview
extern const char** COREDirectedConnectionGetSrc(COREDirectedConnection* directed_connection);
extern const char** COREDirectedConnectionGetSnk(COREDirectedConnection* directed_connection);

extern COREDirectedModule* CORENewDirectedModule(COREModule* m);
extern COREWireable* COREDirectedModuleSel(COREDirectedModule* directed_module, const char** path);
extern COREDirectedConnection** COREDirectedModuleGetConnections(COREDirectedModule* directed_module, int* num_connections);
extern COREDirectedInstance** COREDirectedModuleGetInstances(COREDirectedModule* directed_module, int* num_instances);
extern COREDirectedConnection** COREDirectedModuleGetInputs(COREDirectedModule* directed_module, int* num_connections);
extern COREDirectedConnection** COREDirectedModuleGetOutputs(COREDirectedModule* directed_module, int* num_connections);
// END   : directedview

#endif //COREIR_C_H_
