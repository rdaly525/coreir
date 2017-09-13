#ifndef COREIR_PASSES_HPP_
#define COREIR_PASSES_HPP_

#include "fwd_declare.hpp"

namespace CoreIR {

class Pass {
  
  public:
    enum PassKind {PK_Namespace, PK_Module, PK_Instance, PK_InstanceVisitor, PK_InstanceGraph};
  private:
    PassKind kind;
    //Used as the unique identifier for the pass
    std::string name;
    std::string description;
    //Whether this is an isAnalysis pass
    bool isAnalysis;
    std::vector<std::string> dependencies;
    PassManager* pm;
  public:
    explicit Pass(PassKind kind,std::string name, std::string description, bool isAnalysis) : kind(kind), name(name), description(description), isAnalysis(isAnalysis) {}
    virtual ~Pass() = 0;
    PassKind getKind() const {return kind;}
    
    virtual void releaseMemory() {}
    virtual void setAnalysisInfo() {}
    void addDependency(std::string name) { dependencies.push_back(name);}
    Context* getContext();
    std::string getName() { return name;}
    virtual void print() {}
    
    template<typename T>
    T* getAnalysisPass() {
      assert(pm);
      ASSERT(std::find(dependencies.begin(),dependencies.end(),T::ID)!=dependencies.end(),T::ID + " not declared as a dependency for " + name);
      return (T*) getAnalysisOutside(T::ID);
    }
  private:
    Pass* getAnalysisOutside(std::string ID);
    void addPassManager(PassManager* pm) { this->pm = pm;}
    friend class PassManager;
    friend class Context;
};

typedef Pass* register_pass_t();
typedef void delete_pass_t(Pass*);

//You can do whatever you want here
class NamespacePass : public Pass {
  public:
    explicit NamespacePass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_Namespace,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Namespace;}
    virtual bool runOnNamespace(Namespace* n) = 0;
    virtual void releaseMemory() override {}
    virtual void setAnalysisInfo() override {}
    virtual void print() override {}
};

//Loops through all the modules (with defs) within the namespace
//You can edit the current module but not any other module!
class ModulePass : public Pass {
  public:
    explicit ModulePass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_Module,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Module;}
    virtual bool runOnModule(Module* m) = 0;
    virtual void releaseMemory() override {}
    virtual void setAnalysisInfo() override {}
    virtual void print() override {}

};

//Loops through all instances of all modules
//You can edit the current moduleDef Container
class InstancePass : public Pass {
  public:
    explicit InstancePass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_Instance,name,description,isAnalysis) {}
    static bool classof(const Pass* p) {return p->getKind()==PK_Instance;}
    virtual bool runOnInstance(Instance* i) = 0;
    virtual void releaseMemory() override {}
    virtual void setAnalysisInfo() override {}
    virtual void print() override {}
};

//Run visitor patterns on specific types of instances
//You can edit the current moduleDef Container
class InstanceVisitorPass : public Pass {
  public:
    explicit InstanceVisitorPass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_InstanceVisitor,name,description,isAnalysis) {
      addDependency("createfullinstancemap");
    }
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceVisitor;}
    virtual void releaseMemory() override {}
    virtual void setAnalysisInfo() override {}
    virtual void print() override {}
    virtual void setVisitorInfo() = 0;
    typedef bool (*InstanceVisitor_t)(Instance*);
    void addVisitorFunction(Instantiable* i,InstanceVisitor_t fun);
    bool runOnInstances(Instantiable* i, std::unordered_set<Instance*>& instances);
  private:
    std::unordered_map<Instantiable*,InstanceVisitor_t> visitorMap;
};


class InstanceGraphNode;
//Loops through the InstanceDAG from bottom up. Instane DAG is analogous to CallGraph in LLVM. 
//If the Instance is linked in from a different namespace or is a generator instance, then it will run runOnInstanceNode
//Not allowed 
class InstanceGraphPass : public Pass {
  public:
    
    explicit InstanceGraphPass(std::string name, std::string description, bool isAnalysis=false) : Pass(PK_InstanceGraph,name,description,isAnalysis) {
      addDependency("createinstancegraph");
    }
    static bool classof(const Pass* p) {return p->getKind()==PK_InstanceGraph;}
    virtual bool runOnInstanceGraphNode(InstanceGraphNode& node) = 0;
    virtual void releaseMemory() override {}
    virtual void setAnalysisInfo() override {}
    virtual void print() override {}
};

}


#endif //PASSES_HPP_
