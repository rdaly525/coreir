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

  COREModule* CORENewModule(CORENamespace* ns, char* name, COREType* type, COREGenParams* configparams) {
    GenParams g;
    if (configparams) g =*rcast<GenParams*>(configparams) ;
    return rcast<COREModule*>(rcast<Namespace*>(ns)->newModuleDecl(string(name), rcast<Type*>(type),g));
  }

  COREModuleDef* COREModuleNewDef(COREModule* module) {
    return rcast<COREModuleDef*>(rcast<Module*>(module)->newModuleDef());
  }
  
  COREInstance* COREModuleDefAddModuleInstance(COREModuleDef* module_def, char* name, COREModule* module, COREGenArgs* config) {
    return rcast<COREInstance*>(rcast<ModuleDef*>(module_def)->addInstance(string(name),rcast<Module*>(module),rcast<GenArgs*>(config)));
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

  //Create GenParams
  COREGenParams* CORENewGenParams(COREContext* c) {
    GenParams* genparams = rcast<Context*>(c)->newGenParams(); 
    return rcast<COREGenParams*>(genparams);
  }
  void COREGenParamsAddField(COREGenParams* genparams, char* name, COREGenParam genparam) {
    GenParams* gps = rcast<GenParams*>(genparams);
    gps->emplace(std::string(name),(GenParam) genparam); //TODO a little sketch passing genparam to COREGenParam
  }

  //Create GenArgs
  COREGenArgs* CORENewGenArgs(COREContext* c) {
    GenArgs* gas = rcast<Context*>(c)->newGenArgs({});
    return rcast<COREGenArgs*>(gas);
  }
  void COREGenArgsAddField(COREGenArgs* genargs, char* name, COREGenArg* genarg) {
    GenArgs* gas = rcast<GenArgs*>(genargs);
    gas->addField(std::string(name),rcast<GenArg*>(genarg));
  }
  
  //Create GenArg for int
  COREGenArg* COREGInt(COREContext* c,int i) {
    GenArg* ga = rcast<Context*>(c)->GInt(i);
    return rcast<COREGenArg*>(ga);
  }

  void COREPrintErrors(COREContext* c) {
    rcast<Context*>(c)->printerrors();
  }

}
