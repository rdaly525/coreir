#include "coreir-c/coreir.h"
#include "coreir.h"
#include "common-c.hpp"

namespace CoreIR {


extern "C" {

  void* CORENewMap(COREContext* cc, void* keys, void* values, uint len, COREMapKind kind) {
    Context* c = rcast<Context*>(cc);
    void* ret;
    switch(kind) {
      case(STR2TYPE_ORDEREDMAP) : {
        char** skeys = (char**) keys;
        Type** types = (Type**) values;
        RecordParams* tmap = c->newRecordParams(); 
        for (uint i=0; i<len; ++i) {
          string s = std::string(skeys[i]);
          Type* t = types[i];
          tmap->push_back({s,t});
        }
        ret = (void*) tmap;
        break;
      }
      case (STR2ARG_MAP) : {
        char** skeys = (char**) keys;
        Arg** args = (Arg**) values;
        Args* amap = c->newArgs();
        for (uint i=0; i<len; ++i) {
          string s = std::string(skeys[i]);
          Arg* a = (Arg*) args[i];
          amap->emplace(s,a);
        }
        ret = (void*) amap;
        break;
      }
      case (STR2PARAM_MAP) : {
        char** skeys = (char**) keys;
        Param* params = (Param*) values;
        Params* pmap = c->newParams();
        for (uint i=0; i<len; ++i) {
          string s = std::string(skeys[i]);
          Param p = params[i];
          pmap->emplace(s,p);
        }
        ret = (void*) pmap;
        break;
      }
      default : { cout << "BAD KIND " << kind << endl; c->die(); ret = nullptr;}
    }
    return ret;
  }
  
  COREContext* CORENewContext() {
    return rcast<COREContext*>(newContext());
  }
  void COREDeleteContext(COREContext* c) {
    deleteContext(rcast<Context*>(c));
  }
  
  //TODO change the name of this function
  const char* COREGetInstRefName(COREWireable* iref) {
    const string& name = rcast<Instance*>(iref)->getModuleRef()->getName();
    return name.c_str();
  }

  //TODO change the name to Arg
  COREArg* COREGetConfigValue(COREWireable* i, char* s) {
    string str(s);
    return rcast<COREArg*>(rcast<Instance*>(i)->getConfigArg(str));
  }
  
  
  COREModule* CORELoadModule(COREContext* c, char* filename, bool* err) {
    string file(filename);
    COREModule* m = rcast<COREModule*>(loadModule(rcast<Context*>(c),file,err));
    return m;
  }
  
  void CORESaveModule(COREModule* module, char* filename, bool* err) {
    string file(filename);
    saveModule(rcast<Module*>(module),file,err);
    return;
  }

  CORENamespace* COREGetGlobal(COREContext* c) {
    return rcast<CORENamespace*>(rcast<Context*>(c)->getGlobal());
  }

  COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, void* configparams) {
    Params g;
    if (configparams) g =*rcast<Params*>(configparams) ;
    return rcast<COREModule*>(rcast<Namespace*>(ns)->newModuleDecl(string(name), rcast<Type*>(type),g));
  }

  COREModuleDef* COREModuleNewDef(COREModule* module) {
    return rcast<COREModuleDef*>(rcast<Module*>(module)->newModuleDef());
  }

  COREModuleDef* COREModuleGetDef(COREModule* module) {
    return rcast<COREModuleDef*>(rcast<Module*>(module)->getDef());
  }
  
  COREWireable* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, void* config) {
    return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->addInstance(string(name),rcast<Module*>(module),*rcast<Args*>(config)));
  }

  void COREModuleSetDef(COREModule* module, COREModuleDef* module_def) {
    rcast<Module*>(module)->setDef(rcast<ModuleDef*>(module_def));
  }

  COREDirectedModule* COREModuleGetDirectedModule(COREModule* module) {
      return rcast<COREDirectedModule*>(rcast<Module*>(module)->newDirectedModule());
  }

  void COREModuleDefConnect(COREModuleDef* module_def, COREWireable* a, COREWireable* b) {
    rcast<ModuleDef*>(module_def)->connect(rcast<Wireable*>(a), rcast<Wireable*>(b));
  }

  COREWireable* COREModuleDefGetInterface(COREModuleDef* module_def) {
    return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->getInterface());
  }

  void COREPrintModule(COREModule* m) {
    rcast<Module*>(m)->print();
  }

  void COREPrintModuleDef(COREModuleDef* module_def) {
    rcast<ModuleDef*>(module_def)->print();
  }


  void COREPrintErrors(COREContext* c) {
    rcast<Context*>(c)->printerrors();
  }

  COREWireable* COREModuleDefInstancesGetFirst(COREModuleDef* module_def) {
      return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->getInstancesIterFirst());
  }

  COREWireable* COREModuleDefInstancesGetLast(COREModuleDef* module_def) {
      return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->getInstancesIterLast());
  }

  COREWireable* COREModuleDefInstancesGetNext(COREModuleDef* module_def, COREWireable* curr) {
      return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->getInstancesIterNext(rcast<Instance*>(curr)));
  }

  COREConnection** COREModuleDefGetConnections(COREModuleDef* m, int* numConnections) {
    ModuleDef* module_def = rcast<ModuleDef*>(m);
    unordered_set<Connection> connection_set = module_def->getConnections();
    Context* context = module_def->getContext();
    int size = connection_set.size();
    *numConnections = size;
    Connection* conns = context->newConnectionArray(size);
    Connection** arr = context->newConnectionPtrArray(size);
    int count = 0;
    for (auto it : connection_set) {
      conns[count] = it;
      arr[count] = &conns[count];
      count++;
    }
    return rcast<COREConnection**>(arr);
  }

  COREWireable* COREConnectionGetFirst(COREConnection* c) {
    return rcast<COREWireable*>(rcast<Connection*>(c)->first);
  }

  COREWireable* COREConnectionGetSecond(COREConnection* c) {
    return rcast<COREWireable*>(rcast<Connection*>(c)->second);
  }

  COREWireable** COREWireableGetConnectedWireables(COREWireable* w, int* numWireables) {
    Wireable* wireable = rcast<Wireable*>(w);
    unordered_set<Wireable*> connections_set = wireable->getConnectedWireables();
    Context* context = wireable->getContext();
    int size = connections_set.size();
    *numWireables = size;
    Wireable** arr = context->newWireableArray(size);
    int count = 0;
    for (auto it : connections_set) {
      arr[count] = it;
      count++;
    }
    return rcast<COREWireable**>(arr);
  }

  COREWireable* COREWireableSelect(COREWireable* w, char* sel) {
    return rcast<COREWireable*>(rcast<Wireable*>(w)->sel(string(sel)));
  }

  COREType* COREWireableGetType(COREWireable* wireable) {
    return rcast<COREType*>(rcast<Wireable*>(wireable)->getType());
  }

  COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name) {
    return rcast<COREWireable*>(rcast<ModuleDef*>(m)->sel(string(name)));
  }

  COREModuleDef* COREWireableGetModuleDef(COREWireable* w) {
    return rcast<COREModuleDef*>(rcast<Wireable*>(w)->getModuleDef());
  }

  COREModule* COREModuleDefGetModule(COREModuleDef* m) {
    return rcast<COREModule*>(rcast<ModuleDef*>(m)->getModule());
  }

  const char** COREWireableGetSelectPath(COREWireable* w, int* num_selects) {
    ConstSelectPath path = rcast<Wireable*>(w)->getConstSelectPath();
    Context* c = rcast<Wireable*>(w)->getContext();
    int size = path.size();
    *num_selects = size;
    const char** arr = c->newConstStringArray(size);
    for (int i = 0; i < size; i++) {
      arr[i] = path[i].get().c_str();
    }
    return arr;
  }

  const char* CORENamespaceGetName(CORENamespace* n) {
    return rcast<Namespace*>(n)->getName().c_str();
  }

  const char** COREDirectedConnectionGetSrc(COREDirectedConnection* directed_connection, int* path_len) {
      DirectedConnection* conn = rcast<DirectedConnection*>(directed_connection);
      ConstSelectPath path = conn->getConstSrc();
      Context* c = conn->getContext();
      int size = path.size();
      *path_len = size;
      const char** arr = c->newConstStringArray(size);
      for (int i = 0; i < size; i ++) {
          arr[i] = path[i].get().c_str();
      }
      return arr;
  }

  const char** COREDirectedConnectionGetSnk(COREDirectedConnection* directed_connection, int* path_len) {
      DirectedConnection* conn = rcast<DirectedConnection*>(directed_connection);
      ConstSelectPath path = conn->getConstSnk();
      Context* c = conn->getContext();
      int size = path.size();
      *path_len = size;
      const char** arr = c->newConstStringArray(size);
      for (int i = 0; i < size; i ++) {
          arr[i] = path[i].get().c_str();
      }
      return arr;
  }

  COREDirectedModule* CORENewDirectedModule(COREModule* module) {
      return rcast<COREDirectedModule*>(rcast<Module*>(module)->newDirectedModule());
  }

  COREWireable* COREDirectedModuleSel(COREDirectedModule* directed_module, const char** path, int path_len) {
      SelectPath select_path;
      for (int i = 0; i < path_len; i++) {
          select_path.push_back(std::string(path[i]));
      }
      return rcast<COREWireable*>(rcast<DirectedModule*>(directed_module)->sel(select_path));
  }

  COREDirectedConnection** COREDirectedModuleGetConnections(COREDirectedModule* directed_module, int* num_connections) {
      DirectedModule* module = rcast<DirectedModule*>(directed_module);
      DirectedConnections directed_connections = module->getConnections();
      int size = directed_connections.size();
      *num_connections = size;
      DirectedConnection** ptr_arr = module->getContext()->newDirectedConnectionPtrArray(size);
      int i = 0;
      for (auto directed_connection : directed_connections) {
          ptr_arr[i] = directed_connection;
          i++;
      }
      return rcast<COREDirectedConnection**>(ptr_arr);
  }
  
  COREDirectedInstance** COREDirectedModuleGetInstances(COREDirectedModule* directed_module, int* num_instances) { 
      DirectedModule* module = rcast<DirectedModule*>(directed_module);
      DirectedInstances directed_instances = module->getInstances();
      int size = directed_instances.size();
      *num_instances = size;
      DirectedInstance** ptr_arr = module->getContext()->newDirectedInstancePtrArray(size);
      int i = 0;
      for (auto directed_instance : directed_instances) {
          ptr_arr[i] = directed_instance;
          i++;
      }
      return rcast<COREDirectedInstance**>(ptr_arr);
  }

  COREDirectedConnection** COREDirectedModuleGetInputs(COREDirectedModule* directed_module, int* num_connections) {
      DirectedModule* module = rcast<DirectedModule*>(directed_module);
      DirectedConnections inputs = module->getInputs();
      int size = inputs.size();
      *num_connections = size;
      DirectedConnection** ptr_arr = module->getContext()->newDirectedConnectionPtrArray(size);
      int i = 0;
      for (auto input : inputs) {
          ptr_arr[i] = input;
          i++;
      }
      return rcast<COREDirectedConnection**>(ptr_arr);
  }

  COREDirectedConnection** COREDirectedModuleGetOutputs(COREDirectedModule* directed_module, int* num_connections) {
      DirectedModule* module = rcast<DirectedModule*>(directed_module);
      DirectedConnections outputs = module->getOutputs();
      int size = outputs.size();
      *num_connections = size;
      DirectedConnection** ptr_arr = module->getContext()->newDirectedConnectionPtrArray(size);
      int i = 0;
      for (auto output : outputs) {
          ptr_arr[i] = output;
          i++;
      }
      return rcast<COREDirectedConnection**>(ptr_arr);
  }

  COREDirectedConnection** COREDirectedInstanceGetInputs(COREDirectedInstance* directed_instance, int* num_connections) {
      DirectedInstance* instance = rcast<DirectedInstance*>(directed_instance);
      DirectedConnections inputs = instance->getInputs();
      int size = inputs.size();
      *num_connections = size;
      DirectedConnection** ptr_arr = instance->getContext()->newDirectedConnectionPtrArray(size);
      int i = 0;
      for (auto input : inputs) {
          ptr_arr[i] = input;
          i++;
      }
      return rcast<COREDirectedConnection**>(ptr_arr);
  }

  COREDirectedConnection** COREDirectedInstanceGetOutputs(COREDirectedInstance* directed_instance, int* num_connections) {
      DirectedInstance* instance = rcast<DirectedInstance*>(directed_instance);
      DirectedConnections outputs = instance->getOutputs();
      int size = outputs.size();
      *num_connections = size;
      DirectedConnection** ptr_arr = instance->getContext()->newDirectedConnectionPtrArray(size);
      int i = 0;
      for (auto output : outputs) {
          ptr_arr[i] = output;
          i++;
      }
      return rcast<COREDirectedConnection**>(ptr_arr);
  }

  void COREInstanceGetGenArgs(COREWireable* core_instance, char*** names, COREArg*** args, int* num_args) {
      Instance* instance = rcast<Instance*>(core_instance);
      Args genArgs = instance->getGenArgs();
      int size = genArgs.size();
      Context* context = instance->getContext();
      *names = context->newStringArray(size);
      *args  = (COREArg**) context->newArgPtrArray(size);
      *num_args = size;
      int count = 0;
      for (std::pair<std::string, Arg*> element : genArgs) {
          std::size_t name_length = element.first.size();
          (*names)[count] = context->newStringBuffer(name_length + 1);
          memcpy((*names)[count], element.first.c_str(), name_length + 1);
          (*args)[count] = rcast<COREArg*>(element.second);
          count++;
      }
  }

}//extern "C"
}//CoreIR namespace
