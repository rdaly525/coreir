#ifndef NAMESPACE_CPP_
#define NAMESPACE_CPP_


#include "namespace.hpp"

using namespace std;


TypeGen* Namespace::newTypeGen(string name, string nameFlipped, ArgKinds kinds, TypeGenFun fun) {
      assert(!hasTypeGen(name));
      assert(!hasTypeGen(nameFlipped));
      TypeGen* t = new TypeGen(libname,name,kinds,fun,false);
      TypeGen* tf = new TypeGen(libname,nameFlipped,kinds,fun,true);
      t->setFlipped(tf);
      tf->setFlipped(t);
      tList.emplace(name,t);
      tList.emplace(nameFlipped,tf);
      return t;
    }

void Namespace::addModule(Module* i) {
  iList.emplace(i->getName(),i);
}
void Namespace::addGenerator(Generator* i) {
  iList.emplace(i->getName(),i);
}


Namespace* newNamespace(string name) { return new Namespace(name);}


#endif // NAMESPACE_CPP_
