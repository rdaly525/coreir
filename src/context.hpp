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

namespace CoreIR {

class Context {
  Namespace* global;
  map<string,Namespace*> libs;
  
  uint maxErrors;
  vector<Error> errors;
 
  //Memory management
  TypeCache* cache;
  
  vector<Arg*> argList;
  //vector<Args*> genargsList;
  vector<RecordParams*> recordParamsList;
  vector<Params*> paramsList;
  vector<Instance**> instanceArrays;
  // vector<Connection*> connectionArrays;
  vector<Wireable**> wireableArrays;

  public :
    Context();
    ~Context();
    Namespace* getGlobal() {return global;}
    
    //Error functions
    void error(Error e) { 
      errors.push_back(e);
      if (e.isfatal || errors.size() >= maxErrors) die();
    }
    bool haserror() { return errors.size()>0; }
    void checkerrors() { if (haserror()) die(); }
    void die();
    void printerrors() { 
      for (auto err : errors) cout << "ERROR: " << err.toString() << endl << endl;
    }
    
    bool linkLib(Namespace* defns, Namespace* declns);
    
    Namespace* newNamespace(string name);
    bool hasNamespace(string name) { return libs.count(name) > 0; }
    Namespace* getNamespace(string s);

    Type* Any();
    Type* BitIn();
    Type* BitOut();
    Type* Array(uint n, Type* t);
    Type* Record(RecordParams rp);
    Type* TypeGenInst(TypeGen* tgd, Args args);

    RecordParams* newRecordParams();
    Params* newParams();
    
    Instance** newInstanceArray(int size);
    // Connection* newConnectionArray(int size);
    Wireable** newWireableArray(int size);

    Arg* int2Arg(int i);
    Arg* string2Arg(string s);
    Arg* type2Arg(Type* t);
    
    int arg2Int(Arg* g);
    string arg2String(Arg* g);
    Type* arg2Type(Arg* g);
    
    Type* Flip(Type* t);

};

Module* loadModule(Context* c, string filename, bool* err);
void saveModule(Module* c, string filename, bool* err);

Context* newContext();
void deleteContext(Context* m);

} //CoreIR namespace

#endif //CONTEXT_HPP_
