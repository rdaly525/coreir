#ifndef INSTANTIABLE_HPP_
#define INSTANTIABLE_HPP_


#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hpp"
#include "context.hpp"
#include "types.hpp"
#include "args.hpp"
#include "json.hpp"

#include "moduledef.hpp"
#include "generatordef.hpp"

#include "metadata.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {

class Instantiable {
  protected:
    InstantiableKind kind;
    Namespace* ns;
    string name;
    Metadata metadata;
    Params configparams;
  public :
    Instantiable(InstantiableKind kind, Namespace* ns, string name, Params configparams) : kind(kind), ns(ns), name(name), configparams(configparams) {}
    virtual ~Instantiable() {}
    virtual bool hasDef() const=0;
    virtual string toString() const =0;
    bool isKind(InstantiableKind k) const { return kind==k;}
    InstantiableKind getKind() const { return kind;}
    Module* toModule();
    Generator* toGenerator();
    Context* getContext();
    Params getConfigParams() { return configparams;}
    Metadata getMetadata() { return metadata;}
    string getName() const { return name;}
    virtual json toJson()=0;
    Namespace* getNamespace() const { return ns;}
    friend bool operator==(const Instantiable & l,const Instantiable & r);
};

std::ostream& operator<<(ostream& os, const Instantiable&);


class Generator : public Instantiable {
  Params genparams;
  TypeGen typegen;
  
  //This is memory managed
  GeneratorDef* def;
  
  public :
    Generator(Namespace* ns,string name,Params genparams, TypeGen typegen, Params configparams=Params());
    ~Generator();
    string toString() const;
    json toJson();
    TypeGen getTypeGen() const { return typegen;}
    bool hasDef() const { return !!def; }
    GeneratorDef* getDef() const {return def;}
    void setDef(GeneratorDef* def) { assert(!this->def); this->def = def;}
    void setGeneratorDefFromFun(ModuleDefGenFun fun);
    Params getGenparams() {return genparams;}
};

class Module : public Instantiable {
  Type* type;
  ModuleDef* def;
  
  //Memory Management
  vector<ModuleDef*> mdefList;

  public :
    Module(Namespace* ns,string name, Type* type,Params configparams) : Instantiable(MOD,ns,name,configparams), type(type), def(nullptr) {}
    ~Module();
    bool hasDef() const { return !!def; }
    ModuleDef* getDef() const { return def; } // TODO should probably throw error if does not exist
    void setDef(ModuleDef* def) { this->def = def;}
    ModuleDef* newModuleDef();
    
    string toString() const;
    json toJson();
    Type* getType() { return type;}
    
    void print(void);
};


// Compiling functions.
// resolve, typecheck, and validate will throw errors (for now)

// For now, these functions mutate m. TODO (bad compiler practice probably)

// This is the resolves the Decls and runs the moduleGens
void resolve(Context* c, ModuleDef* m);

//Only resolves the Decls
void resolveDecls(Context* c, ModuleDef* m);

//Only runs the moduleGens
void runGenerators(Context* c, ModuleDef* m);

// This verifies that there are no unconnected wires
//void validate(TypedModuleDef* tm);

// This generates verilog
//string verilog(TypedModuleDef* tm);

// Convieniance that runs resolve, typecheck and validate
// and catches errors;
void compile(Context* c, ModuleDef* m, fstream* f);

}//CoreIR namespace






#endif //INSTANTIABLE_HPP_
