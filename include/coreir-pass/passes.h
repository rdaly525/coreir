#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

void rungenerators(CoreIR::Context* c, CoreIR::Module* m, bool* err);
void flatten(CoreIR::Context* c, CoreIR::Module* m, bool* err);

//Inlines the instance
void inlineInstance(Instance*);

Instance* addPassthrough(Wireable* w,string instname);


//Container: the module that will be modified.
//pattern: the module defines the interface and instances that it will match
//replacement: The Generator that will replace the pattern that was found
//Returns if it modified container (Found a match)
//TODO turn this into a real pass
//bool matchAndReplace(Module* container, Module* pattern, Module* replacement, Args configargs=Args());
//bool matchAndReplace(Module* container, Module* pattern, Module* replacement,std::function<Args(const Instance*)> getConfigArgs);

class ModulePass;
class Pass;
class PassManager {
  Namespace* ns;
  std::map<uint,unordered_map<uint,vector<Pass*>>> passOrdering;
  public:
    explicit PassManager(Namespace* ns) : ns(ns) {}
    ~PassManager();
    //This will memory manage pass.
    void addPass(Pass* p, uint ordering);
    //Returns if graph was modified
    bool run();
  private:
    bool runModulePass(vector<Pass*>& passes);
};

class Pass {
  
  public:
    enum PassKind {PK_Module, PK_InstanceDAG};
  private:
    PassKind kind;
  public:
    explicit Pass(PassKind kind) : kind(kind) {}
    virtual ~Pass() = 0;
    PassKind getKind() const {return kind;}
};

class ModulePass : public Pass {
  public:
    explicit ModulePass() : Pass(PK_Module) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Module;}
    virtual bool runOnModule(Module* m) = 0;

};

class InstanceDAGPass : public Pass {
  public:
    explicit InstanceDAGPass() : Pass(PK_InstanceDAG) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceDAG;}
    virtual bool runOnModule(Module* m) = 0;

};

}


#endif //PASSES_HPP_
