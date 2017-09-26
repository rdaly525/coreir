#ifndef COREIR_CONTEXT_HPP_
#define COREIR_CONTEXT_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class PassManager;
class Pass;
class Context {
  Namespace* global;
  std::map<std::string,Namespace*> namespaces;
  PassManager* pm;

  uint maxErrors;
  std::vector<std::string> errors;
 
  Module* top = nullptr;

  //Unique int
  uint unique=0;

  //Memory management
  TypeCache* cache;
  
  std::unordered_map<void*,ArgPtr> argList;
  std::vector<Args*> argsList;
  std::vector<Arg**> argPtrArrays;
  std::vector<RecordParams*> recordParamsList;
  std::vector<Params*> paramsList;
  std::vector<Connection*> connectionArrays;
  std::vector<Connection**> connectionPtrArrays;
  std::vector<Wireable**> wireableArrays;
  std::vector<const char**> constStringArrays;
  std::vector<char**> stringArrays;
  std::vector<char*> stringBuffers;
  std::vector<DirectedConnection*> directedConnectionArrays;
  std::vector<DirectedConnection**> directedConnectionPtrArrays;
  std::vector<DirectedInstance**> directedInstancePtrArrays;

  public :
    Context();
    ~Context();
    Namespace* getGlobal() {return global;}
    
    //Error functions
    void error(Error& e);
    bool haserror() { return errors.size()>0; }
    void checkerrors() { if (haserror()) die(); }
    void die();
    void printerrors();
    void print();

    //bool linkLib(Namespace* defns, Namespace* declns);
    
    Namespace* newNamespace(std::string name);
    bool hasNamespace(std::string name) { return namespaces.count(name) > 0; }
    Namespace* getNamespace(std::string s);
    Namespace* getCoreirPrims() {return getNamespace("coreir");}
    Module* getModule(std::string ref);
    Generator* getGenerator(std::string ref);
    Instantiable* getInstantiable(std::string ref);
    std::map<std::string,Namespace*> getNamespaces() {return namespaces;}
    void addPass(Pass* p);
    bool runPasses(std::vector<std::string> order,std::vector<std::string> namespaces= std::vector<std::string>({"global"}));

    //TODO figure out a way to hide this (binary/coreir needs it)
    //Do not use unless you really have to.
    PassManager* getPassManager() { return pm;}

    //Factory functions for types
    Type* Bit();
    Type* BitIn();
    Type* Array(uint n, Type* t);
    Type* Record(RecordParams rp=RecordParams());
    Type* Named(std::string nameref);
    Type* Named(std::string nameref, Args args);

    Type* Flip(Type* t);
    Type* In(Type* t);
    Type* Out(Type* t);

    TypeGen* getTypeGen(std::string nameref);

    RecordParams* newRecordParams();
    Params* newParams();
    Args* newArgs();

    //Unique
    std::string getUnique() {
      return "_U" + std::to_string(unique++);
    }
   
    //Sets the top module
    void setTop(std::string topRef);
    void setTop(Module* top);
    bool hasTop() { return !!top;}
    Module* getTop() { return top;}

     
    // C API memory management

    //Saves 
    void* saveArg(ArgPtr arg);
    ArgPtr getSavedArg(void*);
    
    
    Arg** newArgPtrArray(int size);
    Connection* newConnectionArray(int size);
    Connection** newConnectionPtrArray(int size);
    Wireable** newWireableArray(int size);
    const char** newConstStringArray(int size);
    char** newStringArray(int size);
    char* newStringBuffer(int size);
    DirectedConnection** newDirectedConnectionPtrArray(int size);
    DirectedInstance** newDirectedInstancePtrArray(int size);


};

Context* newContext();
void deleteContext(Context* c);


//This will load the namespaces in the file into the context
//If there is a labeled "top", it will be returned in top (if it is not null)
//if no "top" in file, *top == nullptr
bool loadFromFile(Context* c, std::string filename,Module** top=nullptr);

//Save namespace to a file with optional "top" module
bool saveToFile(Namespace* ns, std::string filename,Module* top=nullptr); //This will go away
bool saveToFilePretty(Namespace* ns, std::string filename,Module* top=nullptr);


//Save a module to a dot file (for viewing in graphviz)
bool saveToDot(Module* m, std::string filename);
  
  
//addPassthrough will instance a passthrough Module for Wireable w with name <name>
  //This buffer has interface {"in": Flip(w.Type), "out": w.Type}
  // There will be one connection connecting w to name.in, and all the connections
  // that originally connected to w connecting to name.out which has the same type as w
Instance* addPassthrough(Wireable* w,std::string instname);
bool inlineInstance(Instance*);

typedef Namespace* LoadLibrary_t(Context*);

Namespace* CoreIRLoadLibrary_coreirprims(Context* c);

} //CoreIR namespace

#endif //CONTEXT_HPP_
