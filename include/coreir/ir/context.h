#ifndef COREIR_CONTEXT_HPP_
#define COREIR_CONTEXT_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class PassManager;
class Pass;
class Context {
  Namespace* global;
  std::map<std::string, Namespace*> namespaces;
  PassManager* pm;

  bool symtable = false;

  uint maxErrors;
  std::vector<std::string> errors;

  Module* top = nullptr;

  // Unique int
  uint unique = 0;

  CoreIRLibrary* libmanager;

 public:
  // Used for caching the types
  ValueCache* valuecache;
  TypeCache* typecache;

 private:
  // Memory management
  std::map<void*, Value*> valueList;
  std::vector<Values*> valuesList;
  std::vector<Value**> valuePtrArrays;
  std::vector<ValueType**> valueTypePtrArrays;
  std::vector<Type**> typePtrArrays;
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

  std::vector<void*> scratchPad;

  bool debug = false;

 public:
  Context();
  ~Context();
  Namespace* getGlobal() { return global; }

  // Error functions
  void error(Error& e);
  bool haserror() { return errors.size() > 0; }
  void checkerrors() {
    if (haserror()) die();
  }
  void die();
  void printerrors();
  void print();

  void enSymtable() { symtable = true; }
  bool hasSymtable() { return symtable; }
  Namespace* newNamespace(std::string name);
  bool hasNamespace(std::string name) { return namespaces.count(name) > 0; }
  Namespace* getNamespace(std::string s);
  Namespace* getCoreirPrims() { return getNamespace("coreir"); }
  Module* getModule(std::string ref);
  Generator* getGenerator(std::string ref);
  GlobalValue* getGlobalValue(std::string ref);
  bool hasGenerator(std::string ref);
  bool hasModule(std::string ref);
  bool hasGlobalValue(std::string ref);

  void setDebug(bool debug) { this->debug = debug; }
  bool getDebug() const { return debug; }

  // This function provides scratch memory managed by this context. The memory
  // will be free'd upon deletion of this context.
  // NOTE(rsetaluri): Using memory provided by this function is a *slight*
  // improvment over a true memory leak. Likely, the lifetime of the context
  // will be the lifetime of the program. However, it is preferred to use this
  // function over a true memory leak, sine all such allocations can be
  // localized to calls of this function (and therefore easier to find and fix).
  void* getScratchMemory(size_t size);

  std::map<std::string, Namespace*> getNamespaces();
  void addPass(Pass* p);

  // This will run the following passes in the following namespaces. It defaults
  // only to global, so if you want passes to be run on certain libraries, these
  // need to be specified in the list of namespaces. One subtle thing to note is
  // that an InstanceGraphPass will be run on modules regardless of the
  // namespace. All other Pass Types will only be run on the specified
  // namespaces.
  bool runPasses(
    std::vector<std::string> order,
    std::vector<std::string> namespaces = std::vector<std::string>({"global"}));
  bool runPassesOnAll(std::vector<std::string> order);

  // TODO figure out a way to hide this (binary/coreir needs it)
  // Do not use unless you really have to.
  PassManager* getPassManager() { return pm; }

  // Dynamically load a coreir library
  CoreIRLibrary* getLibraryManager() { return libmanager; }

  // Factory functions for Types
  BitType* Bit();  // Construct a BitOut type
  BitInType* BitIn();
  BitInOutType* BitInOut();
  ArrayType* Array(uint n, Type* t);
  RecordType* Record(RecordParams rp = RecordParams());
  NamedType* Named(std::string nameref);

  // Factory functions for ValueTypes
  AnyType* Any();
  BoolType* Bool();
  IntType* Int();
  BitVectorType* BitVector(int width);
  StringType* String();
  JsonType* Json();
  // CoreIRType* CoreIRType();

  Type* Flip(Type* t);
  Type* In(Type* t);
  Type* Out(Type* t);

  TypeGen* getTypeGen(std::string nameref);
  bool hasTypeGen(std::string nameref);

  RecordParams* newRecordParams();
  Params* newParams();
  Values* newValues();

  // Unique
  std::string getUnique() { return "_U" + std::to_string(unique++); }

  // Sets the top module
  void setTop(std::string topRef);
  void setTop(Module* top);
  void removeTop();
  bool hasTop() { return !!top; }
  Module* getTop() { return top; }

  // C API memory management

  // Saves
  void* saveValue(Value* val);
  Value* getSavedValue(void*);

  Value** newValueArray(int size);
  ValueType** newValueTypeArray(int size);
  Type** newTypeArray(int size);
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

// This will load the namespaces in the file into the context
// If there is a labeled "top", it will be returned in top (if it is not null)
// if no "top" in file, *top == nullptr
bool loadFromFile(Context* c, std::string filename, Module** top = nullptr);

//"Header" is a set of module declarations (should contain no definitions, although it does not check)
// loaded_modules will contain a set of modules which this header declared.
bool loadHeader(Context*c, std::string filename, std::vector<Module*>& loaded_modules);

//"Impl" a set of modules and definitions.
//Each module in this file should already exist as a declaration in the context
bool linkDefinitions(Context*c, std::string filename);

//Given a set of modules, this will save a file with only the listed modules as declarations
bool serializeHeader(Context*c, std::string filename, std::vector<std::string> modules);

//Given a set of modules, this will save all the definitions and their dependencies
bool serializeDefinitions(Context*c, std::string filename, std::vector<std::string> modules);

//This will save a file with top and all its dependencies.
bool serializeToFile(Context* c, std::string filename);

// Save namespace to a file with optional "top" module
bool saveToFile(
  Namespace* ns,
  std::string filename,
  Module* top = nullptr);  // This will go away


bool saveToFile(
  Context* c,
  std::string filename,
  bool nocoreir = true,
  bool no_default_libs = false);


// Save a module to a dot file (for viewing in graphviz)
bool saveToDot(Module* m, std::string filename);
bool saveToDot(Module* m, std::ostream& fout);

// addPassthrough will instance a passthrough Module for Wireable w with name
// <name> This buffer has interface {"in": Flip(w.Type), "out": w.Type}
// There will be one connection connecting w to name.in, and all the connections
// that originally connected to w connecting to name.out which has the same type
// as w
Instance* addPassthrough(Wireable* w, std::string instname);
bool inlineInstance(Instance*);

typedef Namespace* (*LoadLibrary_t)(Context*);

Namespace* CoreIRLoadLibrary_coreirprims(Context* c);

}  // namespace CoreIR

#endif  // CONTEXT_HPP_
