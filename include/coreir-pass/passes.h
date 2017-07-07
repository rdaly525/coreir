#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

void rungenerators(CoreIR::Context* c, CoreIR::Module* m, bool* err);
void flatten(CoreIR::Context* c, CoreIR::Module* m, bool* err);

//Inlines the instance
void inlineInstance(Instance*);

Instance* addPassthrough(Wireable* w,string instname);



class ModulePass;
class Pass;

struct DAGNode {
  Module* m;
  vector<DAGNode*> usedBy;
  vector<DAGNode*> uses;
  explicit DAGNode(Module* m) : m(m) {}
}

class PassManager {
  Namespace* ns;
  typedef std::unordered_map<Module*,DAGNode*> InstanceDAGMap;
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

//Loops through all the modules within the namespace
//You can edit the current module but not any other module!
class ModulePass : public Pass {
  public:
    explicit ModulePass() : Pass(PK_Module) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Module;}
    virtual bool runOnModule(Module* m) = 0;

};

//Loops through the InstanceDAG from bottom up. Instane DAG is analogous to CallGraph in LLVM. 
//If the Instance is linked in from a different namespace or is a generator instance, then it will run runOnInstanceNode
class InstanceDAGPass : public Pass {
  public:
    explicit InstanceDAGPass() : Pass(PK_InstanceDAG) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceDAG;}
    virtual bool runOnModule(Module* m) = 0;
    virtual bool runOnInstanceNode(Instance* i) = 0;
};

}


#endif //PASSES_HPP_
