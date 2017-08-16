#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

class PassManager;

class Pass {
  
  public:
    enum PassKind {PK_Namespace, PK_Module, PK_InstanceGraph};
  private:
    PassKind kind;
    //Used as the unique identifier for the pass
    std::string name;
    std::string description;
    //Whether this is an isAnalysis pass
    bool isAnalysis;
    std::vector<string> dependencies;
    PassManager* pm;
  public:
    explicit Pass(PassKind kind,std::string name, std::string description, bool isAnalysis) : kind(kind), name(name), description(description), isAnalysis(isAnalysis) {}
    virtual ~Pass() = 0;
    PassKind getKind() const {return kind;}
    
    virtual void releaseMemory() {}
    virtual void setAnalysisInfo() {}
    void addDependency(string name) { dependencies.push_back(name);}
    Context* getContext();

    template<typename T>
    T* getAnalysisPass() {
      return (T*) getAnalysisBody(T::ID);
    }
  private:
    Pass* getAnalysisBody(std::string ID);
    void addPassManager(PassManager* pm) { this->pm = pm;}
    friend class PassManager;
};

//You can do whatever you want here
class NamespacePass : public Pass {
  public:
    explicit NamespacePass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_Namespace,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Namespace;}
    virtual void releaseMemory() override {}
    virtual bool runOnNamespace(Namespace* n) = 0;
    virtual void setAnalysisInfo() override {}
    virtual void print() {}
};

//Loops through all the modules within the namespace
//You can edit the current module but not any other module!
class ModulePass : public Pass {
  public:
    explicit ModulePass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_Module,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Module;}
    virtual bool runOnModule(Module* m) = 0;
    virtual void print() {}

};

class InstanceGraphNode;
//Loops through the InstanceDAG from bottom up. Instane DAG is analogous to CallGraph in LLVM. 
//If the Instance is linked in from a different namespace or is a generator instance, then it will run runOnInstanceNode
//Not allowed 
class InstanceGraphPass : public Pass {
  public:
    
    explicit InstanceGraphPass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_InstanceGraph,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceGraph;}
    virtual bool runOnInstanceGraphNode(InstanceGraphNode& node) = 0;
    virtual void print() {}
};

}


#endif //PASSES_HPP_
