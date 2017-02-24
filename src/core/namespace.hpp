#ifndef LIBRARY_HPP_
#define LIBRARY_HPP_

#include <string>
#include <map>
#include "types.hpp" // For TypeGen

using namespace std;

class Instantiable;

class Namespace {
  string libname;
  map<string,Instantiable*> iList;
  map<string,TypeGen*> tList;
  public :
    Namespace(string libname) : libname(libname) {}
    ~Namespace() {
      //for(auto i : iList) delete i.second;
      //for(auto tgd : tgdList) delete tgd.second;
    }
    string getName() { return libname;}
    void newTypeGen(string name, string nameFlipped, ArgKinds kinds, TypeGenFun fun) {
      assert(!hasTypeGen(name));
      assert(!hasTypeGen(nameFlipped));
      TypeGen* t = new TypeGen(libname,name,kinds,fun,false);
      TypeGen* tf = new TypeGen(libname,nameFlipped,kinds,fun,true);
      t->setFlipped(tf);
      tf->setFlipped(t);
      tList.emplace(name,t);
      tList.emplace(nameFlipped,tf);
    }
    TypeGen* getTypeGen(string name) {
      assert(hasTypeGen(name));
      return tList.find(name)->second;
    }
    bool hasTypeGen(string name) {
      return tList.find(name) != tList.end();
    }
    //Instantiable* getInstantiable(string name) {
    //  auto it = iList.find(name);
    //  if (it != iList.end()) return it->second;
    //  throw "Could not find module " + name + " in library " + libname;
    //  return nullptr;
    //}

    //void addInstantiable(Instantiable* i) {
    //  //TODO check if it already there
    //  iList.emplace(i->getName(),i);
    //}
    //TypeGen* getTypeGen(string name) {
    //  auto it = tgdList.find(name);
    //  if (it != tgdList.end()) return it->second;
    //  throw "Could not find module " + name + " in library " libname;
    //  return nullptr;
    //}

    //void addTypeGen(TypeGen* tgd) {
    //  //TODO add both flipped and nonFlipped
    //  //TODO check if it already there
    //  tgdList.emplace(tgd->getName(),tgd);
    //}
    
    void print() {
      cout << "Namespace: " << libname << endl;
      //cout << "  Instantiables:" << endl;
      //for (auto it : iList) cout << "    " << it.second->toString() <<endl;
      cout << endl;
    }

};


#endif //LIBRARY_HPP_
