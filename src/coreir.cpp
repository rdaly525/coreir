extern "C" {
  #include "coreir.h"
}

#include "context.hpp"
#include "passes.hpp"

namespace CoreIR {
template <class T1, class T2>
T1 rcast(T2 in) {
  return reinterpret_cast<T1>(in);

}

extern "C" {
  
 typedef enum {STR2TYPE_MAP,STR2ARG_MAP} COREContainerKind

  void* CORENewContainer(COREContext* c, void** keys, void** values, uint len, COREContainerKind kind);
    if (kind==STR2TYPE_MAP) {
      unordered_map<string,Type*>* tmap = new unordered_map<string,Type*>(); //TODO let context memory manage this
      for (uint i=0; i<len; ++i) {
        string s = std::string((char*) keys[i]);
        Type* t = (Type*) values[i];
        tmap[s] = t;
      }
      return (void*) tmap;
    }
    if (kind==STR2ARG_MAP) {
      unordered_map<string,Arg*>* amap = new unordered
    }
  }
void* COREContainerAt(void*,COREContainerKind kind);
 
  
  COREContext* CORENewContext() {
    return rcast<COREContext*>(newContext());
  }
  void COREDeleteContext(COREContext* c) {
    deleteContext(rcast<Context*>(c));
  }
  COREType* COREAny(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Any());
  }
  COREType* COREBitIn(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitIn());
  }
  COREType* COREBitOut(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitOut());
  }
  COREType* COREArray(COREContext* c,u32 len, COREType* elemType) {
    return rcast<COREType*>(rcast<Context*>(c)->Array(len,rcast<Type*>(elemType)));
  }
  CORERecordParam* CORENewRecordParam(COREContext* context) {
    return rcast<CORERecordParam*>(rcast<Context*>(context)->newRecordParams());
  }
  void CORERecordParamAddField(CORERecordParam* record_param, char* name, COREType* type) {
    rcast<RecordParams*>(record_param)->push_back(myPair<std::string,Type*>(std::string(name), rcast<Type*>(type)));
  }
  COREType* CORERecord(COREContext* context, CORERecordParam* record_param) {
    return rcast<COREType*>(rcast<Context*>(context)->Record(*rcast<RecordParams*>(record_param)));
  }
  //COREType* COREArray(u32 len, COREType* elemType); 
  void COREPrintType(COREType* t) {
    rcast<Type*>(t)->print();
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

  COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, COREParams* configparams) {
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
  
  COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, COREArgs* config) {
    return rcast<COREInstance*>(rcast<ModuleDef*>(module_def)->addInstance(string(name),rcast<Module*>(module),rcast<Args*>(config)));
  }

  void COREModuleAddDef(COREModule* module, COREModuleDef* module_def) {
    rcast<Module*>(module)->addDef(rcast<ModuleDef*>(module_def));
  }

  void COREModuleDefWire(COREModuleDef* module_def, COREWireable* a, COREWireable* b) {
    rcast<ModuleDef*>(module_def)->wire(rcast<Wireable*>(a), rcast<Wireable*>(b));
  }

  COREInterface* COREModuleDefGetInterface(COREModuleDef* module_def) {
    return rcast<COREInterface*>(rcast<ModuleDef*>(module_def)->getInterface());
  }

  CORESelect* COREInstanceSelect(COREInstance* instance, char* field) {
    return rcast<CORESelect*>(rcast<Instance*>(instance)->sel(string(field)));
  }

  CORESelect* COREInterfaceSelect(COREInterface* interface, char* field) {
    return rcast<CORESelect*>(rcast<Interface*>(interface)->sel(string(field)));
  }

  void COREPrintModule(COREModule* m) {
    rcast<Module*>(m)->print();
  }

  void COREPrintModuleDef(COREModuleDef* module_def) {
    rcast<ModuleDef*>(module_def)->print();
  }

  //Create Params
  COREParams* CORENewParams(COREContext* c) {
    Params* genparams = rcast<Context*>(c)->newParams(); 
    return rcast<COREParams*>(genparams);
  }
  void COREParamsAddField(COREParams* genparams, char* name, int genparam) {
    Params* gps = rcast<Params*>(genparams);
    gps->emplace(std::string(name),static_cast<Param>(genparam));
  }

  //Create Args
  COREArgs* CORENewArgs(COREContext* c) {
    Args* gas = rcast<Context*>(c)->args(unordered_map<string,Arg*>());
    return rcast<COREArgs*>(gas);
  }
  void COREArgsAddField(COREArgs* genargs, char* name, COREArg* genarg) {
    Args* gas = rcast<Args*>(genargs);
    gas->addField(std::string(name),rcast<Arg*>(genarg));
  }
  
  //Create Arg for int
  COREArg* COREGInt(COREContext* c,int i) {
    Arg* ga = rcast<Context*>(c)->int2Arg(i);
    return rcast<COREArg*>(ga);
  }

  void COREPrintErrors(COREContext* c) {
    rcast<Context*>(c)->printerrors();
  }

  COREInstance** COREModuleDefGetInstances(COREModuleDef* m, int* numInstances) {
    ModuleDef* module_def = rcast<ModuleDef*>(m);
    unordered_map<string,Instance*> instance_set = module_def->getInstances();
    Context* context = module_def->getContext();
    int size = instance_set.size();
    *numInstances = size;
    Instance** arr = context->newInstanceArray(size);
    int count = 0;
    for (auto it : instance_set) {
      arr[count] = it.second;
      count++;
    }
    return rcast<COREInstance**>(arr);
  }

  // COREConnection* COREModuleDefGetConnections(COREModuleDef* m, int* numConnections) {
  //   ModuleDef* module_def = rcast<ModuleDef*>(m);
  //   unordered_set<Connection> connection_set = module_def->getConnections();
  //   Context* context = module_def->getContext();
  //   int size = connection_set.size();
  //   *numConnections = size;
  //   Connection* arr = context->newConnectionArray(size);
  //   int count = 0;
  //   for (auto it : connection_set) {
  //     memcpy(&arr[count], &it, sizeof(Connection));
  //     count++;
  //   }
  //   return rcast<COREConnection*>(arr);
  // }

  COREWireable* COREConnectionGetFirst(COREConnection* connection) {
    return rcast<COREWireable*>(rcast<Connection*>(connection)->first);
  }

  COREWireable* COREConnectionGetSecond(COREConnection* connection) {
    return rcast<COREWireable*>(rcast<Connection*>(connection)->second);
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

  CORESelect* COREWireableSelect(COREWireable* w, char* name) {
    return rcast<CORESelect*>(rcast<Wireable*>(w)->sel(string(name)));
  }

  COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name) {
    return rcast<COREWireable*>(rcast<ModuleDef*>(m)->sel(string(name)));
  }

  // char*** COREWireableGetWirePath(COREWireable* w) {
  //   WirePath path = rcast<Wireable*>(w)->getPath();
  //   return rcast<COREWirePath>();
  // }

}



}//CoreIR namespace

