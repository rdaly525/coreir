#ifndef CONTEXT_HPP_
#define CONTEXT_HPP_

#include "namespace.hpp"
#include "typecache.hpp"
#include "types.hpp"
#include <string>
#include "enums.hpp"

using namespace std;
class CoreIRContext {
  Namespace* global;
  map<string,Namespace*> libs;
  TypeCache* cache;
  public :
    CoreIRContext();
    ~CoreIRContext();
    Namespace* getGlobal() {return global;}
    void registerLib(Namespace* lib);
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

    //TODO have an interface for GenArgs
  
    Type* Flip(Type* t);
    Generator* newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg);
    Module* newModuleDecl(string name, Type* t);

};

CoreIRContext* newContext();
void deleteContext(CoreIRContext* m);


#endif //CONTEXT_HPP_
