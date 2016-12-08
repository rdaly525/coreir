#include "coreir.hpp"
#include <map>
#include <string>

#include "stdprims.hpp"


Genargs* paramGen(uint n) {
  Genargs* g = new Genargs(Int(32));
  uint32_t* p = (uint32_t*) g->data;
  *p = n;
  return g;
}


// Creates a 4->1 add reduce tree
// in[0] - (+) - (+) - out
// in[1] /     /
// in[2] - (+) 
// in[3] / 
ModuleDef* AddTree(CoreIRContext* c, uint n) {
  GeneratorDecl* addnGen = c->declareGen("stdprims","add2");
  ModuleDecl* addnMod = c->declareMod("stdprims","add2_16");

  Type* inType = Int(n,IN);
  Type* treeType = Record({{"in",Array(inType,4)},{"out",Flip(inType)}});
  string modName = "AddTree"+to_string(n);
  ModuleDef* addTree = new ModuleDef(modName,treeType);
  Wireable* iface = addTree->getInterface();
  Wireable* add_00 = addTree->addInstance("add00",addnGen,paramGen(n));
  Wireable* add_01 = addTree->addInstance("add01",addnMod);
  Wireable* add_1 = addTree->addInstance("add1",addnMod);
  
  addTree->wire(iface->sel("in")->sel(0),add_00->sel("inA"));
  addTree->wire(iface->sel("in")->sel(1),add_00->sel("inB"));
  addTree->wire(iface->sel("in")->sel(2),add_01->sel("inA"));
  addTree->wire(iface->sel("in")->sel(3),add_01->sel("inB"));

  addTree->wire(add_00->sel("out"),add_1->sel("inA"));
  addTree->wire(add_01->sel("out"),add_1->sel("inA"));

  addTree->wire(add_1->sel("out"),iface->sel("out"));

  c->getGlobal()->addModuleDef(addTree);
  return addTree;
}


int main() {
  CoreIRContext* c = newContext();
  
  cout << "Creating a 4->1 tree adder\n";
  ModuleDef* addtree16 = AddTree(c,16);
  addtree16->print();
  
  NameSpace* lib = registerStdPrims(c,"stdprims");
  lib->print();
  c->getGlobal()->print();

  compile(c,addtree16);
  lib->print();
  c->getGlobal()->print();
 
  addtree16->print();
  
  deleteContext(c);
  return 0;
}
