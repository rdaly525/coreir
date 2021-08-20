#include "coreir/ir/module.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/directedview.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/generatordef.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/valuetype.h"

using namespace std;

namespace {

// This will make it a valid coreir string
// Specifically for the case that toString on a type produces square brackets
string sanatizeParamString(string name) {
  string out = name;
  // For type
  out.erase(std::remove(out.begin(), out.end(), '['), out.end());
  out.erase(std::remove(out.begin(), out.end(), ']'), out.end());
  out.erase(std::remove(out.begin(), out.end(), '.'), out.end());
  return out;
}
}  // namespace

namespace CoreIR {

Module::Module(Namespace* ns, std::string name, Type* type, Params modparams)
    : GlobalValue(GVK_Module, ns, name),
      Args(modparams),
      modparams(modparams),
      longname((ns->getName() == "global" ? "" : ns->getName() + "_") + name) {
  ASSERT(
    isa<RecordType>(type),
    "Module type needs to be a record!\n" + type->toString());
  this->type = cast<RecordType>(type);
}

Module::Module(
  Namespace* ns,
  std::string name,
  Type* type,
  Params modparams,
  Generator* g,
  Values genargs)
    : GlobalValue(GVK_Module, ns, name),
      Args(modparams),
      modparams(modparams),
      g(g),
      genargs(genargs) {
  ASSERT(
    isa<RecordType>(type),
    "Module type needs to be a record!\n" + type->toString());
  this->type = cast<RecordType>(type);
  ASSERT(g && genargs.size(), "Missing genargs!");
  if (ns->getName() != "global") {
    this->longname = ns->getName() + "_" + name;
  }
  else {
    this->longname = name;
  }
  for (auto genarg : genargs) {
    this->longname += "__" + genarg.first +
      sanatizeParamString(genarg.second->toString());
  }
}

DirectedModule* Module::newDirectedModule() {
  if (!directedModule) { directedModule = new DirectedModule(this); }
  return directedModule;
}

Module::~Module() {

  for (auto md : mdefList) delete md;
  delete directedModule;
}

ModuleDef* Module::getDef() const {
  // ASSERT(hasDef(),"Missing def:" + this->toString());
  return def;
}

ModuleDef* Module::newModuleDef() {

  ModuleDef* md = new ModuleDef(this);
  mdefList.push_back(md);
  return md;
}

void Module::addDefaultModArgs(Values defaultModArgs) {
  // Check to make sure each arg is in the mod params
  for (auto argmap : defaultModArgs) {
    ASSERT(
      modparams.count(argmap.first),
      "Cannot set default module arg. Param " + argmap.first +
        " Does not exist!");
    this->defaultModArgs[argmap.first] = argmap.second;
  }
}

void Module::setDef(ModuleDef* def, bool validate) {
  if (validate) {
    if (def->validate()) {
      cout << "Error Validating def" << endl;
      this->getContext()->die();
    }
  }
  this->def = def;
  // Directed View is not valid anymore
  delete this->directedModule;
}

string Module::toString() const {
  return "Module: " + this->getRefName() +
    (isGenerated() ? ::CoreIR::toString(genargs) : "") +
    "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

bool Module::runGenerator() {
  ASSERT(g, "Cannot Run Generator of module that is not gen!");
  if (!g->hasDef()) return false;
  if (this->hasDef()) return false;

  ModuleDef* mdef = this->newModuleDef();
  g->getDef()->createModuleDef(mdef, genargs);
  this->setDef(mdef);
  return true;
}

void Module::print(void) const {
  cout << toString() << endl;
  if (def) def->print();
}
bool Module::hasVerilogDef() {
  if (this->getMetaData().count("inline_verilog")) { return true; }
  if (this->getMetaData().count("verilog") > 0) { return true; }
  if (
    this->isGenerated() &&
    this->getGenerator()->getMetaData().count("verilog") > 0) {
    return true;
  }
  return false;
}

bool Module::canSel(std::string sel_str) {
  return this->hasDef() && this->getDef()->canSel(sel_str);
}

bool Module::canSel(SelectPath sel_path) {
  return this->hasDef() && this->getDef()->canSel(sel_path);
}

}  // namespace CoreIR
