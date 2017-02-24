#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include "namespace.hpp"
#include "typecache.hpp"
#include "types.hpp"
#include <string>
#include "enums.hpp"

using namespace std;
class TypeCache;
class CoreIRContext {
  Namespace* global;
  map<string,Namespace*> libs;
  TypeCache* cache;
  public :
    CoreIRContext();
    ~CoreIRContext();
    Namespace* getGlobal() {return global;}
    void registerLib(string name, Namespace* lib) {
      if (libs.find(name) != libs.end()) {
        //TODO how do I deal with linking in headers
        cout << "ERROR: added lib twice: " << name << endl;
        exit(0);
      }
      libs.emplace(name,lib);
    }
    Type* Any();
    Type* BitIn();
    Type* BitOut();
    Type* Array(uint n, Type* t);
    Type* Record(RecordParams rp);
    Type* TypeGenInst(TypeGen* tgd, GenArgs* args);

    GenArg* GInt(int i) { return new GenInt(i); }
    GenArg* GString(string s) { return new GenString(s); }
    GenArg* GType(Type* t) { return new GenType(t); } 
    //TODO have an interface for GenArgs
  
    Type* Flip(Type* t) {
      return t->getFlipped();
    }
};

CoreIRContext* newContext();
void deleteContext(CoreIRContext* m);


#endif //CONTEXT_HPP_
