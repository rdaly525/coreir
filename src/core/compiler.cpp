#ifndef COMPILER_CPP_
#define COMPILER_CPP_

#include "enums.hpp"
#include "coreir.hpp"
#include "typedcoreir.hpp"
#include "verilog.hpp"
#include <sstream>
#include <fstream>

   // ModuleDef* typed = typecheck(m);
void compile(CoreIRContext* c, ModuleDef* m, fstream* f) {
  cout << "Compiling: " << m->toString() << endl;
  try {
    //resolving generators/decls
    resolve(c,m);
    
    //typechecking and return map from mod->typedmod
    typechecked_t* typedmap = typecheck(c,m);
    auto tmap =  typedmap->find(m);
    assert(tmap!=typedmap->end());
    TypedModuleDef* typed = tmap->second;
    
    //validate that there are no dangling wires
    validate(typed); 
    
    //compile to verilog and output to file
    *f << verilog(typed);
    
    //cleanup
    //delete all the typedmap entries
    for (auto it : *typedmap) {
      delete it.second;
    }
    delete typedmap;
  }
  catch(string e) {
    cout << "\nERROR: " << e << endl;
    exit(0);
  }
  
  cout << "Done Compiling" << endl << endl;

}

typedef set<ModuleDef*> resolved_t;
void resolveRec(CoreIRContext* c, ModuleDef* m, resolved_t* resolved);
void resolve(CoreIRContext* c, ModuleDef* m) {
  cout << "Resolving" << endl;
  resolved_t* resolved = new resolved_t;
  resolveRec(c,m,resolved);
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
      modDef = genDef->getGenfun()(c->getGlobal(),inst->getGenArgs());
      inst->replace(modDef);
    } else {
      throw "FUCK";
    }
    resolveRec(c,modDef,resolved);
  }
  resolved->insert(m);
  cout << "  Finished Resolving: " << m->toString() << endl;
}

TypedModuleDef* typecheckRec(CoreIRContext* c, ModuleDef* m, typechecked_t* typechecked);
typechecked_t* typecheck(CoreIRContext* c, ModuleDef* m) {
  cout << "Typechecking" << endl;
  typechecked_t* typechecked = new typechecked_t;
  typecheckRec(c,m,typechecked);
  cout << "Done Typechecking" << endl;
  return typechecked;
}

typedef map<Wireable*,Wireable*> wired_t;
Wireable* getTypedWireable(Wireable* w,wired_t* wired) {
  if (wired->find(w) != wired->end()) {
    return wired->find(w)->second;
  }
  assert(w->isType(SEL)); //Should be Select type
  Select* sw = (Select*) w;
  Wireable* parent = getTypedWireable(sw->getParent(),wired);
  Select* ret = parent->sel(sw->getSelStr());
  assert(ret->isType(TSEL)); // Should be Typed Select
  wired->emplace(sw,ret);
  return ret;
}

TypedModuleDef* typecheckRec(CoreIRContext* c, ModuleDef* m, typechecked_t* typechecked) {
  auto found = typechecked->find(m);
  if (found != typechecked->end()) {
    cout << "  Skipping: " << m->toString() << endl;
    return found->second;
  }

  cout << "  Started Typechecking: " << m->toString() << endl;
  TypedModuleDef* tm = new TypedModuleDef(m->getName(),m->getType());
  tm->addVerilog(m->verilog);
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
    Wireable* twa = getTypedWireable(wiring.first,wired);
    Wireable* twb = getTypedWireable(wiring.second,wired);
    tm->wire(twa,twb); 
  }
  delete wired;
  typechecked->emplace(m,tm);
  
  // TODO I am right here checking if I fucked up here
  cout << "  Finished Typechecking: " << m->toString() << endl;
  return tm;
}

//
void validate(TypedModuleDef* tm) {
  // Module is valid if its interface and all its instances are wired
  
  cout << "Validating Module: " << tm->toString() << endl;
  ostringstream err;
  if(!tm->hasInstances()) {
    cout << "Primitives are by definition valid!\n";
    return;
  }

  TypedWire* tw = castTypedWire(tm->getInterface()->wire);
  tw->checkWired();
  cout << "Interface correct!" << endl;
  for(auto inst : tm->getInstances()) {
    TypedWire* twinst = castTypedWire(inst->wire);
    twinst->checkWired();
  }
  cout << "Done Validating!\n";
}

typedef map<TypedModuleDef*,string> vmods_t;
void verilogRec(TypedModuleDef* tm, vmods_t* vmods);
string verilog(TypedModuleDef* tm) {
  vmods_t* vmods = new vmods_t;
  verilogRec(tm,vmods);
  ostringstream s;
  s << "/* verilator lint_off UNOPTFLAT */" << endl;
  for (auto vmod : *vmods) s << vmod.second << endl << endl;
  delete vmods;
  return s.str();
}

void verilogRec(TypedModuleDef* tm, vmods_t* vmods) {
  if (vmods->find(tm) != vmods->end()) return;
  if (! (tm->verilog=="")) {
    vmods->emplace(tm,tm->verilog);
    return;
  }
  VModule vm = VModule(tm->getName());
  
  // Add all the interface wires to the module
  vector<VWire>* ifcvw = new vector<VWire>; 
  type2VWires(tm->getType(), "",ifcvw);
  for (auto vwire : *ifcvw) {
    vm.addport(vwire);
  }
  delete ifcvw;

  // Declare all instances and wires
  for (auto inst : tm->getInstances()) {
    vm.addstmt("  //Wires for instance "+inst->getInstname());
    
    //Get type
    vector<VWire>* instvw = new vector<VWire>;
    type2VWires(wireable2Type(inst),"", instvw);
    //create Vinstance
    VInstance vinst = VInstance(inst->getInstRef()->getName(),inst->getInstname());
    for (auto vwire : *instvw) {
      // Add connections to instance
      VWire vw = VWire(inst->getInstname() + "_" + vwire.name,vwire.dim,vwire.dir);
      vinst.addport({vwire,vw});
      // Add wire decls to module.
      vm.addstmt(VWireDec(vw));
    }
    delete instvw;
    vm.addstmt(vinst.toString());
    TypedModuleDef* tminst = dynamic_cast<TypedModuleDef*>(inst->getInstRef());
    assert(tminst);
    verilogRec(tminst,vmods);
  }
  

  vm.addstmt("  //Wirings between instances");
  vector<VWire>* vwsa = new vector<VWire>; 
  vector<VWire>* vwsb = new vector<VWire>; 
  for (auto wiring : tm->getWirings()) {
    vwsa->clear();
    vwsb->clear();
    string prefixa = getPrefix(wiring.first,"");
    string prefixb = getPrefix(wiring.second,"");
    type2VWires(wireable2Type(wiring.first),prefixa,vwsa);
    type2VWires(wireable2Type(wiring.second),prefixb,vwsb);
    for (uint i=0; i< vwsa->size(); ++i) {
      vm.addstmt(VAssign((*vwsa)[i],(*vwsb)[i]));
    }
  }
  delete vwsa;
  delete vwsb;
  
  // TODO maybe I should pass vm instead of string
  vmods->emplace(tm,vm.toString());

}



#endif //COMPILER_CPP_
