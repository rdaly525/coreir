#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include "namespace.hpp"
#include "typecache.hpp"
#include "types.hpp"
#include "typegen.hpp"
#include "error.hpp"
#include "common.hpp"
#include "casting/casting.hpp"
#include "directedview.hpp"

#include <string>
#include <unordered_set>
#include <vector>

using namespace std;

namespace CoreIR {

class Context {
  Namespace* global;
  map<string,Namespace*> libs;
  
  uint maxErrors;
  vector<Error> errors;
 
  //Unique int
  uint unique=0;


  //Memory management
  TypeCache* cache;
  
  vector<Arg*> argList;
  vector<Args*> argsList;
  vector<Arg**> argPtrArrays;
  vector<RecordParams*> recordParamsList;
  vector<Params*> paramsList;
  vector<Instance**> instanceArrays;
  vector<Connection*> connectionArrays;
  vector<Connection**> connectionPtrArrays;
  vector<Wireable**> wireableArrays;
  vector<const char**> constStringArrays;
  vector<char**> stringArrays;
  vector<char*> stringBuffers;
  vector<DirectedConnection*> directedConnectionArrays;
  vector<DirectedConnection**> directedConnectionPtrArrays;
  vector<DirectedInstance**> directedInstancePtrArrays;

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
    void print();

    bool linkLib(Namespace* defns, Namespace* declns);
    
    Namespace* newNamespace(string name);
    bool hasNamespace(string name) { return libs.count(name) > 0; }
    Namespace* getNamespace(string s);
    map<string,Namespace*> getNamespaces() {return libs;}

    //Factory functions for types
    Type* Any();
    Type* Bit();
    Type* BitIn();
    Type* Array(uint n, Type* t);
    Type* Record(RecordParams rp);
    Type* Named(string ns, string name);
    Type* Named(string ns, string name, Args args);
    Type* Flip(Type* t);
    Type* In(Type* t);
    Type* Out(Type* t);

    TypeGen* getTypeGen(string ns, string name);

    RecordParams* newRecordParams();
    Params* newParams();
    Args* newArgs();
    
    //Factory functions for args
    Arg* argBool(bool b);
    Arg* argInt(int i);
    Arg* argString(string s);
    Arg* argType(Type* t);

    //Unique
    string getUnique() {
      return "_U" + to_string(unique++);
    }


    Arg** newArgPtrArray(int size);
    Instance** newInstanceArray(int size);
    Connection* newConnectionArray(int size);
    Connection** newConnectionPtrArray(int size);
    Wireable** newWireableArray(int size);
    const char** newConstStringArray(int size);
    char** newStringArray(int size);
    char* newStringBuffer(int size);
    DirectedConnection** newDirectedConnectionPtrArray(int size);
    DirectedInstance** newDirectedInstancePtrArray(int size);


};

Module* loadModule(Context* c, string filename, bool* err);
void saveModule(Module* c, string filename, bool* err);

Context* newContext();
void deleteContext(Context* m);

//addPassthrough will create a passthrough Module for Wireable w with name <name>
  //This buffer has interface {"in": Flip(w.Type), "out": w.Type}
  // There will be one connection connecting w to name.in, and all the connections
  // that originally connected to w connecting to name.out which has the same type as w
Instance* addPassthrough(Context* c, Wireable* w,string instname);



} //CoreIR namespace

#endif //CONTEXT_HPP_
