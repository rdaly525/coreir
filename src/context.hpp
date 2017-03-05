#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include "namespace.hpp"
#include "typecache.hpp"
#include "types.hpp"
#include "error.hpp"
#include <string>
#include "common.hpp"
#include <unordered_set>
#include <vector>

using namespace std;
class CoreIRContext {
  Namespace* global;
  map<string,Namespace*> libs;
  
  //Errors / TODO make errors into seperate class
  uint maxErrors;
  vector<Error> errors;
 
  //Memory management
  TypeCache* cache;
  vector<Namespace*> namespaceList;
  vector<GenArg*> genargList;
  vector<GenArgs*> genargsList;
  vector<Generator*> generatorList;
  vector<Module*> moduleList;
  
  public :
    CoreIRContext();
    ~CoreIRContext();
    Namespace* getGlobal() {return global;}
    
    //Error functions
    void error(Error e) { 
      errors.push_back(e);
      if (e.isfatal || errors.size() >= maxErrors) die();
    }
    bool haserror() { return errors.size()>0; }
    void checkerrors() { if (haserror()) die(); }
    void die() { 
      printerrors();
      delete this; // sketch but okay if exits I guess
      exit(1);
    }
    void printerrors() { 
      for (auto err : errors) cout << "ERROR: " << err.toString() << endl << endl;
    }

    //void clearerror() { err = false; errmsg = "";}
    bool registerLib(Namespace* lib);
    
    bool linkLib(Namespace* defns, Namespace* declns);
    
    Namespace* newNamespace(string name);
    Namespace* getNamespace(string s);

    Type* Any();
    Type* BitIn();
    Type* BitOut();
    Type* Array(uint n, Type* t);
    Type* Record(RecordParams rp);
    Type* TypeGenInst(TypeGen* tgd, GenArgs* args);

    GenArg* GInt(int i);
    GenArg* GString(string s);
    GenArg* GType(Type* t);
    int toInt(GenArg* g);
    string toString(GenArg* g);
    Type* toType(GenArg* g);
    GenArgs* newGenArgs(unordered_map<string,GenArg*> args);   

  
    Type* Flip(Type* t);
    Generator* newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg);
    Module* newModuleDecl(string name, Type* t);



};

CoreIRContext* newContext();
void deleteContext(CoreIRContext* m);


#endif //CONTEXT_HPP_
