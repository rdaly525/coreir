#ifndef COREIR_INSTANTIABLE_HPP_
#define COREIR_INSTANTIABLE_HPP_


#include "fwd_declare.h"
#include "metadata.h"
#include "refname.h"

namespace CoreIR {

class Instantiable : public MetaData, public RefName {
  public :
    enum InstantiableKind {IK_Module,IK_Generator};
    enum LinkageKind {LK_Namespace=0, LK_Generated=1};
  protected:
    InstantiableKind kind;
    
    LinkageKind linkageKind;
  public :
    Instantiable(InstantiableKind kind, Namespace* ns, std::string name) : MetaData(), RefName(ns,name), kind(kind), linkageKind(LK_Namespace) {}
    virtual ~Instantiable() {}
    InstantiableKind getKind() const { return kind;}
    
    virtual std::string toString() const =0;
    virtual void print(void) = 0;
    
    void setLinkageKind(LinkageKind k) { linkageKind = k;}
    LinkageKind getLinkageKind() { return linkageKind; }
    
    void setNamespace(Namespace* ns) {this->ns = ns;}
    friend bool operator==(const Instantiable & l,const Instantiable & r);
    
};

std::ostream& operator<<(std::ostream& os, const Instantiable&);

class Generator : public Instantiable {
  public : 
  
  private :
  
    TypeGen* typegen;
    
    Params genparams;
    Consts defaultGenArgs; 
    
    NameGenFun nameGen=nullptr;
    ModParamsGenFun modParamsGen=nullptr;

    //This is memory managed
    std::unordered_map<Consts,Module*> genCache;
    GeneratorDef* def = nullptr;
  
  public :
    Generator(Namespace* ns,std::string name,TypeGen* typegen, Params genparams);
    ~Generator();
    static bool classof(const Instantiable* i) {return i->getKind()==IK_Generator;}
    std::string toString() const override;
    void print(void) override;
    TypeGen* getTypeGen() const { return typegen;}
    bool hasDef() const { return !!def; }
    GeneratorDef* getDef() const {return def;}
    
    //This will create a fully run module
    //Note, this is stored in the generator itself and is not in the namespace
    Module* getModule(Consts genargs);
    
    //This will transfer memory management of def to this Generator
    void setDef(GeneratorDef* def) { assert(!this->def); this->def = def;}
    void setGeneratorDefFromFun(ModuleDefGenFun fun);
    Params getGenParams() {return genparams;}

    //This will add (and override) default args
    void addDefaultGenArgs(Values defaultGenfigargs);
    Consts getDefaultGenArgs() { return defaultGenArgs;}
  
    void setNameGen(NameGenFun ng) {nameGen = ng;}
    void setModParamsGen(ModParamsGenFun mpg) {modParamsGen = mpg;}
    void setModParamsGen(Params modparams,Consts defaultModArgs) {
      this->modParamsGen = [modparams,defaultModArgs](Context* c,Consts genargs) mutable -> std::pair<Params,Consts> {
        return {modparams,defaultModArgs}; 
      };
    }
    std::pair<Params,Consts> getModParams(Consts genargs) {
      if (modParamsGen) {
        return modParamsGen(getContext(),genargs);
      }
      else {
        return {Params(),Consts()};
      }
    }
};

class Module : public Instantiable {
  Type* type;
  ModuleDef* def = nullptr;
  
  const Params modparams;
  Consts defaultModArgs;

  //std::map<std::string,Arg*> moduleargs;

  //the directedModule View
  DirectedModule* directedModule = nullptr;

  //Memory Management
  std::vector<ModuleDef*> mdefList;

  public :
    Module(Namespace* ns,std::string name, Type* type,Params modparams) : Instantiable(IK_Module,ns,name), type(type), modparams(modparams) {}
    ~Module();
    static bool classof(const Instantiable* i) {return i->getKind()==IK_Module;}
    bool hasDef() const { return !!def; }
    ModuleDef* getDef() const { return def; } 
    //This will validate def
    void setDef(ModuleDef* def, bool validate=true);
   
    ModuleDef* newModuleDef();
    
    const Params& getModParams() const { return modparams;}

    //TODO move this
    DirectedModule* newDirectedModule();
    
    std::string toString() const override;
    Type* getType() { return type;}
    
    void print(void) override;

    //This will add (and override) defaultModArgs
    void addDefaultModArgs(Consts defaultModArgs);
    Consts& getDefaultModArgs() { return defaultModArgs;}

  private :
    //This should be used very carefully. Could make things inconsistent
    friend class InstanceGraphNode;
    void setType(Type* t) {
      type = t;
    }
};


// Compiling functions.
// resolve, typecheck, and validate will throw errors (for now)

// This is the resolves the Decls and runs the moduleGens
//void resolve(Context* c, ModuleDef* m);

//Only resolves the Decls
//void resolveDecls(Context* c, ModuleDef* m);

// This verifies that there are no unconnected wires
//void validate(TypedModuleDef* tm);

// This generates verilog
//string verilog(TypedModuleDef* tm);

// Convieniance that runs resolve, typecheck and validate
// and catches errors;
//void compile(Context* c, ModuleDef* m, fstream* f);

}//CoreIR namespace






#endif //INSTANTIABLE_HPP_
