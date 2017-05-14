#include "coreir-c/coreir.h"
#include "coreir.h"

namespace CoreIR {
template <class T1, class T2>
T1 rcast(T2 in) {
  return reinterpret_cast<T1>(in);

}

extern "C" {

  void* CORENewMap(COREContext* cc, void* keys, void* values, u32 len, COREMapKind kind) {
    Context* c = rcast<Context*>(cc);
    void* ret;
    switch(kind) {
      case(STR2TYPE_ORDEREDMAP) : {
        char** skeys = (char**) keys;
        Type** types = (Type**) values;
        RecordParams* tmap = c->newRecordParams(); 
        for (u32 i=0; i<len; ++i) {
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
        for (u32 i=0; i<len; ++i) {
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
        for (u32 i=0; i<len; ++i) {
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
  const char* COREGetInstRefName(COREInstance* iref) {
    string name = rcast<Instance*>(iref)->getModuleRef()->getName();
    return name.c_str();
  }

  //TODO change the name to Arg
  COREArg* COREGetConfigValue(COREInstance* i, char* s) {
    string str(s);
    return rcast<COREArg*>(rcast<Instance*>(i)->getConfigArg(str));
  }
  
  int COREArg2Int(COREArg* a, bool* err) {
    Arg* arg = rcast<Arg*>(a);
    if (!isa<ArgInt>(arg)) {
      *err = true;
      return 0;
    }
    return arg->get<ArgInt>();
  }
  
  const char* COREArg2Str(COREArg* a, bool* err) {
    Arg* arg = rcast<Arg*>(a);
    if (!isa<ArgString>(arg)) {
      *err = true;
      return "";
    }
    string s = arg->get<ArgString>();
    return s.c_str();
  }
  
  COREType* COREAny(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Any());
  }
  COREType* COREBitIn(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitIn());
  }
  COREType* COREBit(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Bit());
  }
  COREType* COREArray(COREContext* c,u32 len, COREType* elemType) {
    return rcast<COREType*>(rcast<Context*>(c)->Array(len,rcast<Type*>(elemType)));
  }
  COREType* CORERecord(COREContext* context, void* record_param) {
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
  
  COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, void* config) {
    return rcast<COREInstance*>(rcast<ModuleDef*>(module_def)->addInstance(string(name),rcast<Module*>(module),*rcast<Args*>(config)));
  }

  //TODO change name to 'setDef'
  void COREModuleAddDef(COREModule* module, COREModuleDef* module_def) {
    rcast<Module*>(module)->setDef(rcast<ModuleDef*>(module_def));
  }

  void COREModuleDefConnect(COREModuleDef* module_def, COREWireable* a, COREWireable* b) {
    rcast<ModuleDef*>(module_def)->connect(rcast<Wireable*>(a), rcast<Wireable*>(b));
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

  //Create Arg for int
  COREArg* COREInt2Arg(COREContext* c,int i) {
    Arg* ga = rcast<Context*>(c)->argInt(i);
    return rcast<COREArg*>(ga);
  }
  
  COREArg* COREStr2Arg(COREContext* c,char* str) {
    Arg* ga = rcast<Context*>(c)->argString(string(str));
    return rcast<COREArg*>(ga);
  }

  void COREPrintErrors(COREContext* c) {
    rcast<Context*>(c)->printerrors();
  }

  COREInstance** COREModuleDefGetInstances(COREModuleDef* m, u32* numInstances) {
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

  CORESelect* COREWireableSelect(COREWireable* w, char* name) {
    return rcast<CORESelect*>(rcast<Wireable*>(w)->sel(string(name)));
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
    SelectPath path = rcast<Wireable*>(w)->getSelectPath();
    Context* c = rcast<Wireable*>(w)->getContext();
    int size = path.size();
    *num_selects = size;
    const char** arr = c->newConstStringArray(size);
    for (int i = 0; i < size; i++) {
      arr[i] = path[i].c_str();
    }
    return arr;
  }

  const char* CORENamespaceGetName(CORENamespace* n) {
    return rcast<Namespace*>(n)->getName().c_str();
  }
}//extern "C"
}//CoreIR namespace
