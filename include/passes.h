#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

class Pass {
  
  public:
    enum PassKind {PK_Namespace, PK_Module, PK_InstanceGraph};
  private:
    PassKind kind;
    //Used as the unique identifier for the pass
    std::string name;
    std::string description;
    //Whether this is an analysis pass
    std::string isAnalysis;
  public:
    explicit Pass(PassKind kind,std::string name, std::string description, bool isAnalysis) : kind(kind), name(name), description(description), isAnalysis  {}
    virtual ~Pass() = 0;
    PassKind getKind() const {return kind;}
    virtual void setAnalysisInfo() {}
    void addDependency(string name);
};

//You can do whatever you want here
class NamespacePass : public Pass {
  public:
    explicit NamespacePass(std::string name, std::string description, bool isAnalysis) : Pass(PK_Namespace,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Namespace;}
    virtual bool runOnNamespace(Namespace* n) = 0;
    virtual bool runFinalize() {return false;}
};

//Loops through all the modules within the namespace
//You can edit the current module but not any other module!
class ModulePass : public Pass {
  public:
    explicit ModulePass(std::string name, std::string description, bool isAnalysis) : Pass(PK_Module,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Module;}
    virtual bool runOnModule(Module* m) = 0;
    virtual bool runFinalize() {return false;}

};

class InstanceGraphNode;
//Loops through the InstanceDAG from bottom up. Instane DAG is analogous to CallGraph in LLVM. 
//If the Instance is linked in from a different namespace or is a generator instance, then it will run runOnInstanceNode
//Not allowed 
class InstanceGraphPass : public Pass {
  public:
    
    explicit InstanceGraphPass(std::string name, std::string description, bool isAnalysis) : Pass(PK_InstanceGraph,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceGraph;}
    virtual bool runOnInstanceGraphNode(InstanceGraphNode& node) = 0;
    virtual bool runFinalize() {return false;}
};

}


#endif //PASSES_HPP_
