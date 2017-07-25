#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

void rungenerators(CoreIR::Context* c, CoreIR::Module* m, bool* err);
void flatten(CoreIR::Context* c, CoreIR::Module* m, bool* err);

//Inlines the instance
bool inlineInstance(Instance*);

Instance* addPassthrough(Wireable* w,string instname);

class Pass {
  
  public:
    enum PassKind {PK_Module, PK_InstanceGraph};
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

class InstanceGraphNode;
//Loops through the InstanceDAG from bottom up. Instane DAG is analogous to CallGraph in LLVM. 
//If the Instance is linked in from a different namespace or is a generator instance, then it will run runOnInstanceNode
//Not allowed 
class InstanceGraphPass : public Pass {
  public:
    
    explicit InstanceGraphPass() : Pass(PK_InstanceGraph) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceGraph;}
    virtual bool runOnInstanceGraphNode(InstanceGraphNode& node) = 0;
};

}


#endif //PASSES_HPP_
