#ifndef COMPILER_CPP_
#define COMPILER_CPP_

#include "enums.hpp"
#include "coreir.hpp"
#include "typedcoreir.hpp"


TypedModuleDef* typecheck(CoreIRContext* c, ModuleDef* m);
   // ModuleDef* typed = typecheck(m);
void compile(CoreIRContext* c, ModuleDef* m) {
  cout << "Compiling: " << m->toString() << endl;
  resolve(c,m);
  TypedModuleDef* typed = typecheck(c,m);
  cout << "Done Compiling" << endl << endl;
  typed->print();
  delete typed;
}
typedef set<ModuleDef*> resolved_t;
//TODO should I hae this throw and catch errors? probs not
void resolveRec(CoreIRContext* c, ModuleDef* m, resolved_t* resolved);
void resolve(CoreIRContext* c, ModuleDef* m) {
  cout << "Resolving" << endl;
  resolved_t* resolved = new resolved_t;
  try {
    resolveRec(c,m,resolved);
  } 
  catch(string e) {
    cout << "ERROR: " << e << endl;
    delete resolved;
    exit(0);
  }
  delete resolved;
  cout << "Done Resolving" << endl;
}

//This function mutates the current moduleDef recursively to
//  replace all ModuleDecl with ModuleDef
//  replace all GeneratorDecl with ModuleDef
//resolved keeps getting added to
void resolveRec(CoreIRContext* c, ModuleDef* m, resolved_t* resolved) {
  
  //Do not do any recompute if module already resolved
  if (resolved->find(m) != resolved->end()) return;
  cout << "  Started Resolving: " << m->toString() << endl;

  //For each instance compute if necessary and then resolve recursively
  for (auto inst : m->getInstances()) {
    Instantiable* instRef = inst->getInstRef();
    ModuleDef* modDef;
    string nameSpace = instRef->getNameSpaceStr();
    if (instRef->isType(MDEF) ) {
      modDef = (ModuleDef*) instRef;
    }
    else if (instRef->isType(MDEC) ) {
      NameSpace* n = c->nameSpaceLookup(nameSpace);
      modDef = n->moduleDefLookup(instRef->getName());
      inst->replace(modDef);
    }
    else if (instRef->isType(GDEC) ) {
      NameSpace* n = c->nameSpaceLookup(nameSpace);
      GeneratorDef* genDef = n->generatorDefLookup(instRef->getName());
      //Generate the module in the global namespace
      modDef = genDef->getGenfun()(c->getGlobal(),inst->getGenargs());
      inst->replace(modDef);
    } else {
      throw "FUCK";
    }
    resolveRec(c,modDef,resolved);
  }
  resolved->insert(m);
  cout << "  Finished Resolving: " << m->toString() << endl;
}

typedef map<ModuleDef*,TypedModuleDef*> typechecked_t;
TypedModuleDef* typecheckRec(CoreIRContext* c, ModuleDef* m, typechecked_t* typechecked);
TypedModuleDef* typecheck(CoreIRContext* c, ModuleDef* m) {
  cout << "Typechecking" << endl;
  typechecked_t* typechecked = new typechecked_t;
  TypedModuleDef* tm;
  try {
    tm = typecheckRec(c,m,typechecked);
  } 
  catch(string e) {
    cout << "ERROR: " << e << endl;
    delete typechecked;
    exit(0);
  }
  delete typechecked;
  cout << "Done Typechecking" << endl;
  return tm;
}

typedef map<Wireable*,Wireable*> wired_t;

Wireable* getTypedWire(Wireable* w,wired_t* wired) {
  if (wired->find(w) != wired->end()) return wired->find(w)->second;
  assert(w->isType(SEL)); //Should be Select type
  Select* sw = (Select*) w;
  Wireable* parent = getTypedWire(sw->getParent(),wired);
  Select* ret = parent->sel(sw->getSelStr());
  assert(ret->isType(TSEL)); // Should be Typed Select
  wired->emplace(sw,ret);
  return ret;
}

TypedModuleDef* typecheckRec(CoreIRContext* c, ModuleDef* m, typechecked_t* typechecked) {
  auto found = typechecked->find(m);
  if (found != typechecked->end()) return found->second;

  cout << "  Started Typechecking: " << m->toString() << endl;
  TypedModuleDef* tm = new TypedModuleDef(m->getName(),m->getType());
  wired_t* wired = new wired_t();
  wired->emplace(m->getInterface(),tm->getInterface());
  for (auto inst : m->getInstances()) {
    Instantiable* iref = inst->getInstRef();
    if (!iref->isType(MDEF)) {
      throw "Inst " + inst->toString() + "Is not a ModuleDef!\n  Can only typecheck resolved generator/modules";
    }
    ModuleDef* mref = (ModuleDef*) iref;
    TypedModuleDef* tmref = typecheckRec(c,mref,typechecked);
    Instance* tinst = tm->addInstance(inst->getInstname(),tmref);
    wired->emplace(inst,tinst);
  }
  for (auto wiring : m->getWirings() ) {
    Wireable* twa = getTypedWire(wiring.first,wired);
    Wireable* twb = getTypedWire(wiring.second,wired);
    tm->wire(twa,twb); 
  }
  delete wired;
  cout << "  Finished Typechecking: " << m->toString() << endl;
  return tm;
}

//
bool Validate(TypedModuleDef* tm) {
  //TODO
  return false;
  // Circuit is valid if its interface and all its instances are _wired
  //if(c->isPrimitive()) {
  //  cout << "Primitives are by definition valid!\n";
  //  return true;
  //}
  //bool valid = true;
  //Module* mod = (Module*) c;
  //if (!mod->getInterface()->checkWired()) {
  //  cout << "Inteface is Not fully connected!\n";
  //  return false;
  //}
  //vector<Instance*> insts = mod->getInstances();
  //vector<Instance*>::iterator it;
  //for(it=insts.begin(); it!=insts.end(); ++it) {
  //  if (!(*it)->checkWired() ) {
  //    cout << "Instance: " << (*it)->_string() << " is not fully connected\n";
  //    valid = false;
  //  }
  //}
  //cout << "You have a valid Module!\n";
  //return valid;
}


#endif //COMPILER_CPP_
