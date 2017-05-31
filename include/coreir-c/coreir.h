#ifndef COREIR_C_H_
#define COREIR_C_H_

#include "ctypes.h"

typedef unsigned int uint;
typedef int COREBool;

// API for types
#include "coreir-types.h"

//API for Args
#include "coreir-args.h"

//keys and values will not be freed
void* CORENewMap(COREContext* c, void* keys, void* values, uint len, COREMapKind kind);

//Context COREreater/deleters
extern COREContext* CORENewContext();
extern void COREDeleteContext(COREContext*);


extern COREModule* CORELoadModule(COREContext* c, char* filename, COREBool* err);

//Errors:
//Cannot open file for reading/writing
extern void CORESaveModule(COREModule* module, char* filename, COREBool* err);
extern CORENamespace* COREGetGlobal(COREContext* c);
extern const char* COREGetInstRefName(COREWireable* iref);

//Errors:
//  Invalid arg: Module name already exists
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, void* configparams);

extern void COREPrintModule(COREModule* m);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
//extern COREModuleDef* COREModuleGetDef(COREModule* m);
void COREModuleSetDef(COREModule* module, COREModuleDef* module_def);
extern COREDirectedModule* COREModuleGetDirectedModule(COREModule* module);

//Errors:
//  Invalid arg: instance name already exists
extern COREWireable* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, void* config); //config will be Args*
extern COREWireable* COREModuleDefGetInterface(COREModuleDef* m);
extern COREArg* COREGetConfigValue(COREWireable* i, char* s); 

//Errors:
//  Wire Error;
//  Typechecking errors
extern void COREModuleDefConnect(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern COREWireable* COREWireableSelect(COREWireable* w, char* sel);
extern COREWireable** COREModuleDefGetInstances(COREModuleDef* m, uint* numInstances);
extern COREConnection** COREModuleDefGetConnections(COREModuleDef* m, int* numWires);
extern COREWireable* COREConnectionGetFirst(COREConnection* c);
extern COREWireable* COREConnectionGetSecond(COREConnection* c);
extern COREWireable** COREWireableGetConnectedWireables(COREWireable* wireable, int* numWireables);
extern COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name);
extern COREModuleDef* COREWireableGetModuleDef(COREWireable* w);
extern COREModule* COREModuleDefGetModule(COREModuleDef* m);
extern const char** COREWireableGetSelectPath(COREWireable* w, int* num_selects);
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
extern COREDirectedConnection** COREDirectedInstanceGetOutputs(COREDirectedInstance* directed_instance, int* num_connections);
extern COREDirectedConnection** COREDirectedInstanceGetInputs(COREDirectedInstance* directed_instance, int* num_connections);
// END   : directedview

#endif //COREIR_C_H_
