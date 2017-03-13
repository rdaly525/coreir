extern "C" {
  #include "coreir.h"
}

#include "context.hpp"
#include "passes.hpp"

template <class T1, class T2>
T1 rcast(T2 in) {
  return reinterpret_cast<T1>(in);

}

extern "C" {
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
  
  COREModule* CORELoadModule(COREContext* c, char* filename) {
    string file(filename);
    return rcast<COREModule*>(loadModule(rcast<Context*>(c),file));
  }
  
  bool CORESaveModule(COREModule* module, char* filename) {
    string file(filename);
    return rcast<COREModule*>(saveModule(rcast<Module*>(module),file));
  }

  CORENamespace* COREGetGlobal(COREContext* c) {
    return rcast<CORENamespace*>(rcast<Context*>(c)->getGlobal());
  }

  COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type) {
    return rcast<COREModule*>(rcast<Namespace*>(ns)->newModuleDecl(string(name), rcast<Type*>(type)));
  }

  COREModuleDef* COREModuleNewDef(COREModule* module) {
    return rcast<COREModuleDef*>(rcast<Module*>(module)->newModuleDef());
  }
  
  COREInstance* COREModuleDefAddInstanceModule(COREModuleDef* module_def, char* name, COREModule* module) {
    return rcast<COREInstance*>(rcast<ModuleDef*>(module_def)->addInstanceModule(string(name),rcast<Module*>(module)));
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

  COREInstance** COREModuleDefGetInstances(COREModuleDef* m, int* numInstances) {
    ModuleDef* module_def = rcast<ModuleDef*>(m);
    set<Instance*> instance_set = module_def->getInstances();
    Context* context = module_def->getContext();
    int size = instance_set.size();
    *numInstances = size;
    Instance** arr = context->newInstanceArray(size);
    int count = 0;
    for (auto it : instance_set) {
      arr[count] = it;
      count++;
    }
    return rcast<COREInstance**>(arr);
  }

  COREWiring* COREModuleDefGetWires(COREModuleDef* m, int* numWires) {
    ModuleDef* module_def = rcast<ModuleDef*>(m);
    set<Wiring> wire_set = module_def->getWires();
    Context* context = module_def->getContext();
    int size = wire_set.size();
    *numWires = size;
    Wiring* arr = context->newWiringArray(size);
    int count = 0;
    for (auto it : wire_set) {
      arr[count] = it;
      count++;
    }
    return rcast<COREWiring*>(arr);
  }

}
