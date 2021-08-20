#ifndef COREIR_MODULE_HPP_
#define COREIR_MODULE_HPP_

#include "args.h"
#include "coreir/primitive.h"
#include "fwd_declare.h"
#include "globalvalue.h"

namespace CoreIR {

class Module : public GlobalValue, public Args, public VerilogPrimitive {
  RecordType* type;
  ModuleDef* def = nullptr;
  std::map<std::string,Module*> linkedModules;

  const Params modparams;
  Values defaultModArgs;

  Generator* g = nullptr;
  Values genargs;

  std::string longname;

  // the directedModule View
  DirectedModule* directedModule = nullptr;

  // Memory Management
  std::vector<ModuleDef*> mdefList;

 public:
  Module(Namespace* ns, std::string name, Type* type, Params modparams);
  Module(
    Namespace* ns,
    std::string name,
    Type* type,
    Params modparams,
    Generator* g,
    Values genargs);
  virtual ~Module();
  static bool classof(const GlobalValue* i) {
    return i->getKind() == GVK_Module;
  }
  bool hasDef() const { return !!def; }
  ModuleDef* getDef() const;
  // This will validate def
  void setDef(ModuleDef* def, bool validate = true);

  void linkModule(std::string key, Module* mod) {
    // TODO: Should we raise en error if a key is used twice?
    this->linkedModules[key] = mod;
  };

  std::map<std::string,Module*> getLinkedModules() const {
    return linkedModules;
  };

  bool hasVerilogDef();

  ModuleDef* newModuleDef();

  const Params& getModParams() const { return modparams; }

  // TODO move this
  DirectedModule* newDirectedModule();

  std::string toString() const override;
  RecordType* getType() { return type; }

  bool isGenerated() const { return !!g; }
  Generator* getGenerator() {
    ASSERT(
      isGenerated(),
      "Cannot getGenerator, is not a generated module: " + this->getRefName());
    return g;
  }
  Values getGenArgs() {
    ASSERT(
      isGenerated(),
      "Cannot getGenArgs, is not a generated module: " + this->getRefName());
    return genargs;
  }

  // Only runs a generator if the module does not already have a definition
  bool runGenerator();
  std::string getLongName() const { return longname; }

  void print(void) const override;

  // This will add (and override) defaultModArgs
  void addDefaultModArgs(Values defaultModArgs);
  Values& getDefaultModArgs() { return defaultModArgs; }

  bool canSel(std::string sel_str);
  bool canSel(SelectPath sel_path);

 private:
  // This should be used very carefully. Could make things inconsistent
  friend class InstanceGraphNode;
  void setType(RecordType* t) { this->type = t; }
};

}  // namespace CoreIR

#endif
