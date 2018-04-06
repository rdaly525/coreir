#ifndef COREIR_C_H_
#define COREIR_C_H_

#include "ctypes.h"

typedef unsigned int uint;
typedef int COREBool;

// API for types
#include "coreir-types.h"

//API for Values
#include "coreir-values.h"

//keys and values will not be freed
void* CORENewMap(COREContext* c, void* keys, void* values, uint len, COREMapKind kind);

//Context COREreater/deleters
extern COREContext* CORENewContext();
extern void COREDeleteContext(COREContext*);
extern COREType* COREContextNamedType(COREContext* context, const char* namespace_, const char* type_name);

extern COREValueType* COREContextBool(COREContext* context);
extern COREValueType* COREContextInt(COREContext* context);
extern COREValueType* COREContextBitVector(COREContext* context);
extern COREValueType* COREContextString(COREContext* context);
extern COREValueType* COREContextString(COREContext* context);

extern bool COREContextRunPasses(COREContext* ctx, char** passes, int num_passes,
                                           char** namespaces, int num_namespaces);


extern COREModule* CORELoadModule(COREContext* c, char* filename, COREBool* err);

//Errors:
//Cannot open file for reading/writing
extern void CORESaveModule(COREModule* module, char* filename, COREBool* err);
extern CORENamespace* COREGetGlobal(COREContext* c);
extern CORENamespace* COREGetNamespace(COREContext* c, char* name);

extern COREModule* COREGetModuleRef(COREWireable* iref);
extern bool COREModuleIsGenerated(COREModule* mod);
extern COREGenerator* COREModuleGetGenerator(COREModule* mod);
void COREModuleGetGenArgs(COREModule* mod, char*** names, COREValue** args, int* num_args);
extern const char* COREModuleGetName(COREModule* module);
extern const char* COREGeneratorGetName(COREModule* module);
void COREGeneratorGetGenParams(COREGenerator* core_gen, char*** names, COREValueType*** params, int* num_params);
COREModule* COREGeneratorGetModule(COREGenerator* core_gen, void* genargs);

//Errors:
//  Invalid arg: Module name already exists
extern COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, void* configparams);
extern COREGenerator* CORENamespaceGetGenerator(CORENamespace* _namespace, const char* name);
extern COREModule* CORENamespaceGetModule(CORENamespace* _namespace, const char* name);
extern void CORENamespaceGetGenerators(CORENamespace* core_namespace, char*** keys, COREGenerator*** values, int* num_items);
extern void CORENamespaceGetModules(CORENamespace* core_namespace, char*** keys, COREModule*** values, int* num_items);
extern bool CORENamespaceHasGenerator(CORENamespace* _namespace, const char* name);
extern bool CORENamespaceHasModule(CORENamespace* _namespace, const char* name);

extern void COREPrintModule(COREModule* m);
extern const char* COREModuleGetName(COREModule* module);
extern COREModuleDef* COREModuleNewDef(COREModule* m);
//extern COREModuleDef* COREModuleGetDef(COREModule* m);
void COREModuleSetDef(COREModule* module, COREModuleDef* module_def);
extern COREDirectedModule* COREModuleGetDirectedModule(COREModule* module);

//Errors:
//  Invalid arg: instance name already exists
extern COREWireable* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, void* config); //config will be Args*
extern COREWireable* COREModuleDefAddGeneratorInstance(COREModuleDef* module_def, char* name, COREGenerator* generator, void* genargs, void* config);

extern COREWireable* COREModuleDefGetInterface(COREModuleDef* m);
extern COREValue* COREGetModArg(COREWireable* i, char* s);
extern void COREGetModArgs(COREWireable* core_wireable, char*** keys, COREValue*** values, int* num_items);
extern bool COREHasModArg(COREWireable* i, char* s);

//Errors:
//  Wire Error;
//  Typechecking errors
extern void COREModuleDefConnect(COREModuleDef* module_def, COREWireable* a, COREWireable* b);
extern COREWireable* COREWireableSelect(COREWireable* w, char* sel);
extern COREBool COREWireableCanSelect(COREWireable* w, char* sel);
extern COREWireable* COREModuleDefInstancesIterBegin(COREModuleDef* module_def);
extern COREWireable* COREModuleDefInstancesIterEnd(COREModuleDef* module_def);
extern COREWireable* COREModuleDefInstancesIterNext(COREModuleDef* module_def, COREWireable* curr);
extern COREConnection** COREModuleDefGetConnections(COREModuleDef* m, int* numWires);
extern COREWireable* COREConnectionGetFirst(COREConnection* c);
extern COREWireable* COREConnectionGetSecond(COREConnection* c);
extern COREWireable** COREWireableGetConnectedWireables(COREWireable* wireable, int* numWireables);
extern COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name);
extern COREModuleDef* COREWireableGetContainer(COREWireable* w);
extern COREModule* COREModuleDefGetModule(COREModuleDef* m);
extern const char** COREWireableGetSelectPath(COREWireable* w, int* num_selects);
extern void COREPrintErrors(COREContext* c);
extern const char* CORENamespaceGetName(CORENamespace* n);
extern COREType* COREWireableGetType(COREWireable* wireable);

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

int COREValueTypeGetKind(COREValueType* value_type);

void COREFree(void* ptr);

#endif //COREIR_C_H_
