#include <fstream>
#include <strings.h>
#include "common-c.hpp"
#include "coreir-c/coreir.h"
#include "coreir.h"
#include "coreir/common/defer.hpp"
#include "coreir/common/logging_lite.hpp"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/definitions/memoryVerilog.hpp"
#include "coreir/ir/json.h"
#include "coreir/passes/analysis/verilog.h"

using namespace std;
namespace CoreIR {

namespace {

void lowerModuleMap(
    const std::map<std::string, Module*>& modules,
    char*** keys,
    COREModule*** values,
    int* size) {
  *size = modules.size();
  *keys = static_cast<char**>(malloc((*size) * sizeof(char*)));
  *values = static_cast<COREModule**>(malloc((*size) * sizeof(COREModule*)));
  int i = 0;
  for (auto const& item : modules) {
    const char* key = item.first.c_str();
    (*keys)[i] = static_cast<char*>(malloc(strlen(key) + 1));
    strcpy((*keys)[i], key);
    (*values)[i] = rcast<COREModule*>(item.second);
    i++;
  }
}

}  // namespace

extern "C" {

void* CORENewMap(
  COREContext* cc,
  void* keys,
  void* values,
  uint len,
  COREMapKind kind) {
  Context* c = rcast<Context*>(cc);
  void* ret;
  switch (kind) {
  case (STR2TYPE_ORDEREDMAP): {
    char** skeys = (char**)keys;
    Type** types = (Type**)
      values;  // TODO Sketch, this is doing an implicit rcast
    RecordParams* tmap = c->newRecordParams();
    for (uint i = 0; i < len; ++i) {
      string s = std::string(skeys[i]);
      Type* t = types[i];
      tmap->push_back({s, t});
    }
    ret = (void*)tmap;
    break;
  }
  case (STR2VALUE_MAP): {
    char** skeys = (char**)keys;
    Value** args = (Value**)values;
    Values* amap = c->newValues();
    for (uint i = 0; i < len; ++i) {
      string s = std::string(skeys[i]);
      Value* a = args[i];
      amap->emplace(s, a);
    }
    ret = (void*)amap;
    break;
  }
  case (STR2VALUETYPE_MAP): {
    char** skeys = (char**)keys;
    ValueType** vtypes = (ValueType**)values;
    Params* pmap = c->newParams();
    for (uint i = 0; i < len; ++i) {
      string s = std::string(skeys[i]);
      pmap->emplace(s, vtypes[i]);
    }
    ret = (void*)pmap;
    break;
  }
  default: {
    cout << "BAD KIND " << kind << endl;
    c->die();
    ret = nullptr;
  }
  }
  return ret;
}

COREContext* CORENewContext() { return rcast<COREContext*>(newContext()); }
void COREDeleteContext(COREContext* c) { deleteContext(rcast<Context*>(c)); }

COREType* COREContextNamed(
  COREContext* context,
  const char* namespace_,
  const char* type_name) {
  return rcast<COREType*>(rcast<Context*>(context)->Named(
    std::string(namespace_) + "." + std::string(type_name)));
}
COREType* COREContextFlip(COREContext* context, COREType* type) {
  return rcast<COREType*>(rcast<Context*>(context)->Flip(rcast<Type*>(type)));
}

COREValueType* COREContextBool(COREContext* context) {
  return rcast<COREValueType*>(rcast<Context*>(context)->Bool());
}

COREValueType* COREContextInt(COREContext* context) {
  return rcast<COREValueType*>(rcast<Context*>(context)->Int());
}

COREValueType* COREContextBitVector(COREContext* context, int width) {
  return rcast<COREValueType*>(rcast<Context*>(context)->BitVector(width));
}

COREValueType* COREContextString(COREContext* context) {
  return rcast<COREValueType*>(rcast<Context*>(context)->String());
}

COREValueType* COREContextCoreIRType(COREContext* context) {
  return rcast<COREValueType*>(CoreIRType::make(rcast<Context*>(context)));
}

COREModule* COREGetModuleRef(COREWireable* iref) {
  Module* m = cast<Instance>(rcast<Wireable*>(iref))->getModuleRef();
  return rcast<COREModule*>(m);
}

bool COREContextRunPasses(
  COREContext* ctx,
  char** passes,
  int num_passes,
  char** namespaces,
  int num_namespaces) {
  Context* context = rcast<Context*>(ctx);
  vector<string> vec_passes;
  vector<string> vec_namespaces;
  for (int i = 0; i < num_passes; i++) { vec_passes.emplace_back(passes[i]); }
  for (int i = 0; i < num_namespaces; i++) {
    vec_namespaces.emplace_back(namespaces[i]);
  }
  return context->runPasses(vec_passes, vec_namespaces);
}

void COREContextSetTop(COREContext* context, COREModule* module) {
  rcast<Context*>(context)->setTop(rcast<Module*>(module));
}

bool CORECompileToVerilog(
  COREContext* ctx,
  COREModule* top,
  char* filename,
  int num_libs,
  char** libs,
  char* split,
  char* product,
  bool inline_,
  bool verilator_debug,
  bool disable_width_cast) {
  auto context = reinterpret_cast<Context*>(ctx);
  auto module = reinterpret_cast<Module*>(top);
  context->setTop(module->getRefName());

  // TODO(rsetaluri): This code duplicates much of the verilog compilation
  // codepath in the coreir.cpp binary. We should extract this into a common
  // place.
  std::vector<std::string> libraries;
  for (int i = 0; i < num_libs; i++) {
    std::string lib(libs[i]);
    context->getLibraryManager()->loadLib(lib);
  }
  // TODO(rsetaluri): Have option to output this or not.
  CoreIRLoadVerilog_coreir(context);
  CoreIRLoadVerilog_corebit(context);

  std::string verilog_pass = "verilog";
  if (inline_) verilog_pass += " -i";
  if (verilator_debug) verilog_pass += " -y";
  if (disable_width_cast) verilog_pass += " -w";
  std::vector<std::string> namespaces{"global"};
  std::vector<std::string> passes{
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    verilog_pass};
  context->runPasses(passes, namespaces);
  auto pass = static_cast<Passes::Verilog*>(
    context->getPassManager()->getAnalysisPass("verilog"));
  defer(pass->clear());

  std::string output_dir(split);
  // Split files, and write to output_dir.
  if (output_dir != "") {
    std::string product_file(product);
    std::unique_ptr<std::string> product_file_ptr;
    if (product_file != "") {
      product_file_ptr.reset(new std::string(product));
    }
    pass->writeToFiles(output_dir, std::move(product_file_ptr), "v");
    return true;
  }
  // Do not split; write to filename.
  std::string outfile(filename);
  std::ofstream fout(outfile);
  if (not fout.is_open()) {
    LOG(DEBUG) << "Cannot open file '" + outfile + "' to compile to verilog";
    return false;
  }
  pass->writeToStream(fout);
  return true;
}

bool COREInlineInstance(COREWireable* inst) {
  Instance* i = cast<Instance>(rcast<Wireable*>(inst));
  return inlineInstance(i);
}

COREWireable* COREAddPassthrough(COREWireable* corew) {
  Wireable* w = rcast<Wireable*>(corew);
  Context* c = w->getContext();
  Instance* inst = addPassthrough(w, "pt" + c->getUnique());
  return rcast<COREWireable*>(cast<Wireable>(inst));
}

void CORERemoveInstance(COREWireable* inst) {
  Instance* i = cast<Instance>(rcast<Wireable*>(inst));
  ModuleDef* def = i->getContainer();
  def->removeInstance(i);
}

void COREGetModArgs(
  COREWireable* core_wireable,
  char*** keys,
  COREValue*** values,
  int* num_items) {
  Values modargs = cast<Instance>(rcast<Wireable*>(core_wireable))
                     ->getModArgs();
  *num_items = modargs.size();
  *keys = (char**)malloc(*num_items * sizeof(char*));
  *values = (COREValue**)malloc(*num_items * sizeof(COREValue*));
  int i = 0;
  for (auto const& item : modargs) {
    const char* key = item.first.c_str();
    (*keys)[i] = (char*)malloc(strlen(key) + 1);
    strcpy((*keys)[i], key);
    (*values)[i] = rcast<COREValue*>(item.second);
    i++;
  }
}

COREValue* COREGetModArg(COREWireable* i, char* s) {
  string str(s);
  Values modargs = cast<Instance>(rcast<Wireable*>(i))->getModArgs();
  ASSERT(modargs.count(str) > 0, "ModArgs does not contain field: " + str);
  return rcast<COREValue*>(modargs[str]);
}

bool COREHasModArg(COREWireable* i, char* s) {
  string str(s);
  Values modargs = cast<Instance>(rcast<Wireable*>(i))->getModArgs();
  return modargs.count(str) > 0;
}

bool COREModuleHasDef(COREModule* module) {
  return rcast<Module*>(module)->hasDef();
}

// TODO update C api
// This can return nullptr
// bool loadFromFile(Context* c, string filename,Module** top);
COREModule* CORELoadModule(COREContext* c, char* filename, bool* err) {
  string file(filename);
  Module* top = nullptr;
  Context* context = rcast<Context*>(c);
  bool correct = loadFromFile(context, file, &top);
  if (!top) {
    Error e;
    e.message("No top in file :" + string(filename));
    context->error(e);
    *err = true;
  }
  *err = !correct;
  return rcast<COREModule*>(top);
}

void CORESaveContext(
  COREContext* context,
  char* filename,
  bool nocoreir,
  bool no_default_libs,
  bool* err) {

  string file(filename);
  std::cout << filename << std::endl;
  bool correct = saveToFile(
    rcast<Context*>(context),
    file,
    nocoreir,
    no_default_libs);
  *err = !correct;
  return;
}

void CORESerializeToFile(COREContext* cc, char* filename, COREBool* err) {
  string file(filename);
  Context* c = rcast<Context*>(cc);
  bool correct = serializeToFile(c, file);
  *err = !correct;
  return;
}


// bool saveToFile(Namespace* ns, string filename,Module* top=nullptr);
void CORESaveModule(COREModule* module, char* filename, bool* err) {
  string file(filename);
  Module* top = rcast<Module*>(module);
  bool correct = saveToFile(top->getNamespace(), file, top);
  *err = !correct;
  return;
}

void CORESerializeHeader(COREContext* cc, char* filename, char** modules, uint num_modules, COREBool* err) {
  Context* c = rcast<Context*>(cc);
  string file(filename);
  vector<string> vec_modules;
  for (uint i=0; i< num_modules; ++i) {
    vec_modules.emplace_back(modules[i]);
  }
  bool correct = serializeHeader(c, file, vec_modules);
  *err = !correct;
  return;
}

void CORESerializeDefinitions(COREContext* cc, char* filename, char** modules, uint num_modules, COREBool* err) {
  Context* c = rcast<Context*>(cc);
  string file(filename);
  vector<string> vec_modules;
  for (uint i = 0; i < num_modules; ++i) {
    vec_modules.emplace_back(modules[i]);
  }
  bool correct = serializeDefinitions(c, file, vec_modules);
  *err = !correct;
  return;
}

void CORELoadHeader(COREContext* cc, char* filename, char*** modules, uint* num_modules, COREBool* err) {
  Context* c = rcast<Context*>(cc);
  std::string file(filename);
  std::vector<Module*> loaded_modules;
  bool correct = loadHeader(c, file, loaded_modules);
  *err = !correct;
  if (correct) {
    *num_modules = loaded_modules.size();
    *modules = c->newStringArray(loaded_modules.size());
    int count = 0;
    for (auto m : loaded_modules) {
      std::string mref = m->getRefName();
      std::size_t name_length = mref.size();
      (*modules)[count] = c->newStringBuffer(name_length + 1);
      memcpy((*modules)[count], mref.c_str(), name_length + 1);
      count++;
    }
  }
  else {
    *num_modules = 0;
  }
}

void CORELinkDefinitions(COREContext* cc, char* filename, COREBool* err) {
  Context* c = rcast<Context*>(cc);
  std::string file(filename);
  bool correct = linkDefinitions(c, file);
  *err = !correct;
}


CORENamespace* COREGetGlobal(COREContext* c) {
  return rcast<CORENamespace*>(rcast<Context*>(c)->getGlobal());
}

CORENamespace* COREGetNamespace(COREContext* c, char* name) {
  return rcast<CORENamespace*>(
    rcast<Context*>(c)->getNamespace(std::string(name)));
}

bool COREHasNamespace(COREContext* c, char* name) {
  return rcast<Context*>(c)->hasNamespace(std::string(name));
}

CORENamespace* CORENewNamespace(COREContext* c, char* name) {
  return rcast<CORENamespace*>(
    rcast<Context*>(c)->newNamespace(std::string(name)));
}

CORENamespace* COREGlobalValueGetNamespace(COREGlobalValue* value) {
  return rcast<CORENamespace*>(rcast<GlobalValue*>(value)->getNamespace());
}

COREModule* CORENewModule(
  CORENamespace* ns,
  char* name,
  COREType* type,
  void* modparams) {
  Params g;
  if (modparams) g = *rcast<Params*>(modparams);
  return rcast<COREModule*>(
    rcast<Namespace*>(ns)->newModuleDecl(string(name), rcast<Type*>(type), g));
}

bool COREModuleIsGenerated(COREModule* mod) {
  return rcast<Module*>(mod)->isGenerated();
}

COREType* COREModuleGetType(COREModule* module) {
  return rcast<COREType*>(rcast<Module*>(module)->getType());
}

COREGenerator* COREModuleGetGenerator(COREModule* mod) {
  return rcast<COREGenerator*>(rcast<Module*>(mod)->getGenerator());
}

void COREModuleGetGenArgs(
  COREModule* core_mod,
  char*** names,
  COREValue*** args,
  int* num_args) {
  Module* mod = rcast<Module*>(core_mod);
  Values genValues = mod->getGenArgs();
  int size = genValues.size();
  Context* context = mod->getContext();
  *names = context->newStringArray(size);
  *args = (COREValue**)context->newValueArray(size);
  *num_args = size;
  int count = 0;
  for (auto element : genValues) {
    std::size_t name_length = element.first.size();
    (*names)[count] = context->newStringBuffer(name_length + 1);
    memcpy((*names)[count], element.first.c_str(), name_length + 1);
    (*args)[count] = rcast<COREValue*>(element.second);
    count++;
  }
}

void COREModuleGetModParams(
  COREModule* core_mod,
  char*** names,
  COREValueType*** params,
  int* num_params) {
  Module* mod = rcast<Module*>(core_mod);
  Params modParams = mod->getModParams();
  int size = modParams.size();
  Context* context = mod->getContext();
  *names = context->newStringArray(size);
  *params = (COREValueType**)context->newValueTypeArray(size);
  *num_params = size;
  int count = 0;
  for (auto element : modParams) {
    std::size_t name_length = element.first.size();
    (*names)[count] = context->newStringBuffer(name_length + 1);
    memcpy((*names)[count], element.first.c_str(), name_length + 1);
    (*params)[count] = rcast<COREValueType*>(element.second);
    count++;
  }
}

const char* COREModuleGetMetaData(COREModule* core_mod) {
  Module* mod = rcast<Module*>(core_mod);
  string mstr = mod->getMetaData().dump();
  std::size_t len = mstr.size() + 1;
  char* cstr = (char*)malloc(len);
  strcpy(cstr, mstr.c_str());
  return cstr;
}

const char* COREInstanceGetMetaData(COREWireable* core_inst) {
  auto w = rcast<Wireable*>(core_inst);
  ASSERT(isa<Instance>(w), "Wireable needs to be an instnace");
  Instance* inst = cast<Instance>(w);
  std::string metadata = inst->getMetaData().dump();
  auto copy = static_cast<char*>(
      w->getContext()->getScratchMemory(metadata.size() + 1));
  strcpy(copy, metadata.c_str());
  return copy;
}

const char* COREModuleGetName(COREModule* module) {
  return rcast<Module*>(module)->getName().c_str();
}

const char* COREGeneratorGetName(COREGenerator* gen) {
  return rcast<Generator*>(gen)->getName().c_str();
}

void COREGeneratorGetGenParams(
  COREGenerator* core_gen,
  char*** names,
  COREValueType*** params,
  int* num_params) {
  Generator* gen = rcast<Generator*>(core_gen);
  Params genParams = gen->getGenParams();
  int size = genParams.size();
  Context* context = gen->getContext();
  *names = context->newStringArray(size);
  *params = (COREValueType**)context->newValueTypeArray(size);
  *num_params = size;
  int count = 0;
  for (auto element : genParams) {
    std::size_t name_length = element.first.size();
    (*names)[count] = context->newStringBuffer(name_length + 1);
    memcpy((*names)[count], element.first.c_str(), name_length + 1);
    (*params)[count] = rcast<COREValueType*>(element.second);
    count++;
  }
}

COREModule* COREGeneratorGetModule(COREGenerator* core_gen, void* genargs) {
  return rcast<COREModule*>(
    rcast<Generator*>(core_gen)->getModule(*rcast<Values*>(genargs)));
}

COREModuleDef* COREModuleNewDef(COREModule* module) {
  return rcast<COREModuleDef*>(rcast<Module*>(module)->newModuleDef());
}

COREModuleDef* COREModuleGetDef(COREModule* module) {
  return rcast<COREModuleDef*>(rcast<Module*>(module)->getDef());
}

COREWireable* COREModuleDefAddModuleInstance(
  COREModuleDef* module_def,
  char* name,
  COREModule* module,
  void* mod) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)
                                ->addInstance(
                                  string(name),
                                  rcast<Module*>(module),
                                  *rcast<Values*>(mod)));
}

COREWireable* COREModuleDefAddGeneratorInstance(
  COREModuleDef* module_def,
  char* name,
  COREGenerator* generator,
  void* genargs,
  void* mod) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)
                                ->addInstance(
                                  string(name),
                                  rcast<Generator*>(generator),
                                  *rcast<Values*>(genargs),
                                  *rcast<Values*>(mod)));
}

void COREModuleSetDef(COREModule* module, COREModuleDef* module_def) {
  rcast<Module*>(module)->setDef(rcast<ModuleDef*>(module_def));
}

COREDirectedModule* COREModuleGetDirectedModule(COREModule* module) {
  return rcast<COREDirectedModule*>(
    rcast<Module*>(module)->newDirectedModule());
}

bool COREModuleLinkModule(char* key, COREModule* source, COREModule* target) {
  auto s = rcast<Module*>(source);
  auto t = rcast<Module*>(target);
  s->linkModule(std::string(key), t);
  return true;
}

bool COREModuleGetLinkedModules(
    COREModule* source, char*** keys, COREModule*** targets, int* size) {
  auto s = rcast<Module*>(source);
  auto ts = s->getLinkedModules();
  lowerModuleMap(ts, keys, targets, size);
  return true;
}

bool COREModuleLinkDefaultModule(COREModule* source, COREModule* target) {
  auto s = rcast<Module*>(source);
  auto t = rcast<Module*>(target);
  s->linkDefaultModule(t);
  return true;
}

bool COREModuleHasDefaultLinkedModule(COREModule* source) {
  auto s = rcast<Module*>(source);
  return s->hasDefaultLinkedModule();
}

COREModule* COREModuleGetDefaultLinkedModule(COREModule* source) {
  auto s = rcast<Module*>(source);
  auto linked = s->getDefaultLinkedModule();
  return rcast<COREModule*>(linked);
}

void COREModuleDefConnect(
  COREModuleDef* module_def,
  COREWireable* a,
  COREWireable* b) {
  rcast<ModuleDef*>(module_def)
    ->connect(rcast<Wireable*>(a), rcast<Wireable*>(b));
}

void COREModuleDefDisconnect(
  COREModuleDef* module_def,
  COREWireable* a,
  COREWireable* b) {
  rcast<ModuleDef*>(module_def)
    ->disconnect(rcast<Wireable*>(a), rcast<Wireable*>(b));
}

COREWireable* COREModuleDefGetInterface(COREModuleDef* module_def) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)->getInterface());
}

void COREPrintModule(COREModule* m) { rcast<Module*>(m)->print(); }

void COREPrintModuleDef(COREModuleDef* module_def) {
  rcast<ModuleDef*>(module_def)->print();
}

void COREPrintErrors(COREContext* c) { rcast<Context*>(c)->printerrors(); }

COREWireable* COREModuleDefInstancesIterBegin(COREModuleDef* module_def) {
  return rcast<COREWireable*>(
    rcast<ModuleDef*>(module_def)->getInstancesIterBegin());
}

COREWireable* COREModuleDefInstancesIterEnd(COREModuleDef* module_def) {
  return rcast<COREWireable*>(
    rcast<ModuleDef*>(module_def)->getInstancesIterEnd());
}

COREWireable* COREModuleDefInstancesIterNext(
  COREModuleDef* module_def,
  COREWireable* curr) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(module_def)
                                ->getInstancesIterNext(rcast<Instance*>(curr)));
}

COREConnection** COREModuleDefGetConnections(
  COREModuleDef* m,
  int* numConnections) {
  ModuleDef* module_def = rcast<ModuleDef*>(m);
  auto connection_set = module_def->getConnections();
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

COREWireable** COREWireableGetConnectedWireables(
  COREWireable* w,
  int* numWireables) {
  Wireable* wireable = rcast<Wireable*>(w);
  set<Wireable*> connections_set = wireable->getConnectedWireables();
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

COREBool COREWireableCanSelect(COREWireable* w, char* sel) {
  return rcast<Wireable*>(w)->canSel(string(sel));
}

COREWireable* COREWireableGetParent(COREWireable* cw) {
  Wireable* w = rcast<Wireable*>(cw);
  ASSERT(isa<Select>(w), "Can only get the parent of a Select");
  return rcast<COREWireable*>(cast<Select>(w)->getParent());
}

COREType* COREWireableGetType(COREWireable* wireable) {
  return rcast<COREType*>(rcast<Wireable*>(wireable)->getType());
}

COREWireable* COREModuleDefSelect(COREModuleDef* m, char* name) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(m)->sel(string(name)));
}

bool COREModuleDefCanSelect(COREModuleDef* m, char* name) {
  return rcast<COREWireable*>(rcast<ModuleDef*>(m)->canSel(string(name)));
}

COREModuleDef* COREWireableGetContainer(COREWireable* w) {
  return rcast<COREModuleDef*>(rcast<Wireable*>(w)->getContainer());
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
  for (int i = 0; i < size; i++) { arr[i] = path[i].get().c_str(); }
  return arr;
}

const char* CORENamespaceGetName(CORENamespace* n) {
  return rcast<Namespace*>(n)->getName().c_str();
}

COREGenerator* CORENamespaceGetGenerator(
  CORENamespace* _namespace,
  const char* name) {
  return rcast<COREGenerator*>(
    rcast<Namespace*>(_namespace)->getGenerator(std::string(name)));
}

bool CORENamespaceHasGenerator(CORENamespace* _namespace, const char* name) {
  std::map<std::string, Generator*> generators = rcast<Namespace*>(_namespace)
                                                   ->getGenerators();
  auto it = generators.find(name);
  return it != generators.end();
}

COREModule* CORENamespaceGetModule(
  CORENamespace* _namespace,
  const char* name) {
  return rcast<COREModule*>(
    rcast<Namespace*>(_namespace)->getModule(std::string(name)));
}

void CORENamespaceGetModules(
  CORENamespace* core_namespace,
  char*** keys,
  COREModule*** values,
  int* num_items) {

  auto modules = rcast<Namespace*>(core_namespace)->getModules();
  lowerModuleMap(modules, keys, values, num_items);
}

void CORENamespaceGetGenerators(
  CORENamespace* core_namespace,
  char*** keys,
  COREGenerator*** values,
  int* num_items) {

  std::map<std::string, Generator*>
    generators = rcast<Namespace*>(core_namespace)->getGenerators();

  *num_items = generators.size();
  *keys = (char**)malloc(*num_items * sizeof(char*));
  *values = (COREGenerator**)malloc(*num_items * sizeof(COREGenerator*));
  int i = 0;
  for (auto const& item : generators) {
    const char* key = item.first.c_str();
    (*keys)[i] = (char*)malloc(strlen(key) + 1);
    strcpy((*keys)[i], key);
    (*values)[i] = rcast<COREGenerator*>(item.second);
    i++;
  }
}

bool CORENamespaceHasModule(CORENamespace* _namespace, const char* name) {
  std::map<std::string, Module*> modules = rcast<Namespace*>(_namespace)
                                             ->getModules();
  auto it = modules.find(name);
  return it != modules.end();
}

const char** COREDirectedConnectionGetSrc(
  COREDirectedConnection* directed_connection,
  int* path_len) {
  DirectedConnection* conn = rcast<DirectedConnection*>(directed_connection);
  ConstSelectPath path = conn->getConstSrc();
  Context* c = conn->getContext();
  int size = path.size();
  *path_len = size;
  const char** arr = c->newConstStringArray(size);
  for (int i = 0; i < size; i++) { arr[i] = path[i].get().c_str(); }
  return arr;
}

const char** COREDirectedConnectionGetSnk(
  COREDirectedConnection* directed_connection,
  int* path_len) {
  DirectedConnection* conn = rcast<DirectedConnection*>(directed_connection);
  ConstSelectPath path = conn->getConstSnk();
  Context* c = conn->getContext();
  int size = path.size();
  *path_len = size;
  const char** arr = c->newConstStringArray(size);
  for (int i = 0; i < size; i++) { arr[i] = path[i].get().c_str(); }
  return arr;
}

COREDirectedModule* CORENewDirectedModule(COREModule* module) {
  return rcast<COREDirectedModule*>(
    rcast<Module*>(module)->newDirectedModule());
}

COREWireable* COREDirectedModuleSel(
  COREDirectedModule* directed_module,
  const char** path,
  int path_len) {
  SelectPath select_path;
  for (int i = 0; i < path_len; i++) {
    select_path.push_back(std::string(path[i]));
  }
  return rcast<COREWireable*>(
    rcast<DirectedModule*>(directed_module)->sel(select_path));
}

COREDirectedConnection** COREDirectedModuleGetConnections(
  COREDirectedModule* directed_module,
  int* num_connections) {
  DirectedModule* module = rcast<DirectedModule*>(directed_module);
  DirectedConnections directed_connections = module->getConnections();
  int size = directed_connections.size();
  *num_connections = size;
  DirectedConnection** ptr_arr = module->getContext()
                                   ->newDirectedConnectionPtrArray(size);
  int i = 0;
  for (auto directed_connection : directed_connections) {
    ptr_arr[i] = directed_connection;
    i++;
  }
  return rcast<COREDirectedConnection**>(ptr_arr);
}

COREDirectedInstance** COREDirectedModuleGetInstances(
  COREDirectedModule* directed_module,
  int* num_instances) {
  DirectedModule* module = rcast<DirectedModule*>(directed_module);
  DirectedInstances directed_instances = module->getInstances();
  int size = directed_instances.size();
  *num_instances = size;
  DirectedInstance** ptr_arr = module->getContext()
                                 ->newDirectedInstancePtrArray(size);
  int i = 0;
  for (auto directed_instance : directed_instances) {
    ptr_arr[i] = directed_instance;
    i++;
  }
  return rcast<COREDirectedInstance**>(ptr_arr);
}

COREDirectedConnection** COREDirectedModuleGetInputs(
  COREDirectedModule* directed_module,
  int* num_connections) {
  DirectedModule* module = rcast<DirectedModule*>(directed_module);
  DirectedConnections inputs = module->getInputs();
  int size = inputs.size();
  *num_connections = size;
  DirectedConnection** ptr_arr = module->getContext()
                                   ->newDirectedConnectionPtrArray(size);
  int i = 0;
  for (auto input : inputs) {
    ptr_arr[i] = input;
    i++;
  }
  return rcast<COREDirectedConnection**>(ptr_arr);
}

COREDirectedConnection** COREDirectedModuleGetOutputs(
  COREDirectedModule* directed_module,
  int* num_connections) {
  DirectedModule* module = rcast<DirectedModule*>(directed_module);
  DirectedConnections outputs = module->getOutputs();
  int size = outputs.size();
  *num_connections = size;
  DirectedConnection** ptr_arr = module->getContext()
                                   ->newDirectedConnectionPtrArray(size);
  int i = 0;
  for (auto output : outputs) {
    ptr_arr[i] = output;
    i++;
  }
  return rcast<COREDirectedConnection**>(ptr_arr);
}

COREDirectedConnection** COREDirectedInstanceGetInputs(
  COREDirectedInstance* directed_instance,
  int* num_connections) {
  DirectedInstance* instance = rcast<DirectedInstance*>(directed_instance);
  DirectedConnections inputs = instance->getInputs();
  int size = inputs.size();
  *num_connections = size;
  DirectedConnection** ptr_arr = instance->getContext()
                                   ->newDirectedConnectionPtrArray(size);
  int i = 0;
  for (auto input : inputs) {
    ptr_arr[i] = input;
    i++;
  }
  return rcast<COREDirectedConnection**>(ptr_arr);
}

COREDirectedConnection** COREDirectedInstanceGetOutputs(
  COREDirectedInstance* directed_instance,
  int* num_connections) {
  DirectedInstance* instance = rcast<DirectedInstance*>(directed_instance);
  DirectedConnections outputs = instance->getOutputs();
  int size = outputs.size();
  *num_connections = size;
  DirectedConnection** ptr_arr = instance->getContext()
                                   ->newDirectedConnectionPtrArray(size);
  int i = 0;
  for (auto output : outputs) {
    ptr_arr[i] = output;
    i++;
  }
  return rcast<COREDirectedConnection**>(ptr_arr);
}

void COREModuleAddMetaDataStr(COREModule* module, char* key, char* value) {
  const auto json = nlohmann::json::parse(std::string(value));
  rcast<Module*>(module)->getMetaData()[key] = json;
}

void COREWireableAddMetaDataStr(
  COREWireable* wireable,
  char* key,
  char* value) {
  const auto json = nlohmann::json::parse(std::string(value));
  rcast<Wireable*>(wireable)->getMetaData()[key] = json;
}

void COREModuleDefAddConnectionMetaDataStr(
  COREModuleDef* module_def,
  COREWireable* a,
  COREWireable* b,
  char* key,
  char* value) {
  const auto json = nlohmann::json::parse(std::string(value));
  rcast<ModuleDef*>(module_def)
    ->getMetaData(rcast<Wireable*>(a), rcast<Wireable*>(b))[key] = json;
}

const char* COREInstanceGetInstname(COREWireable* instance) {
  return rcast<Instance*>(instance)->getInstname().c_str();
}

const char* COREInstanceGetModArgs(COREWireable* instance) {
  return rcast<Instance*>(instance)->getInstname().c_str();
}

bool CORETypeIsInput(COREType* type) { return rcast<Type*>(type)->isInput(); }

bool CORETypeIsOutput(COREType* type) { return rcast<Type*>(type)->isOutput(); }

int COREValueTypeGetKind(COREValueType* value_type) {
  return rcast<ValueType*>(value_type)->getKind();
}

void COREFree(void* ptr) { free(ptr); }

const char* COREGetVersion() { return COREIR_VERSION; }

const char* COREGetRevision() { return GIT_SHA1; }

}  // extern "C"
}  // namespace CoreIR
