#include "coreir.hpp"
#include <map>
#include <string>

#include "stdprims.hpp"


void* paramGen(uint n) {
  uint* p = (uint*) malloc(sizeof(uint));
  *p = n;
  return (void*) p;
}

// Creates a 4->1 add reduce tree
// in[0] - (+) - (+) - out
// in[1] /     /
// in[2] - (+) 
// in[3] / 
Module* AddTree(CoreIRContext* c, uint n) {
  OpaqueGenerator* addnGen = c->declareGen("stdprims","add2");
  OpaqueModule* addnMod = c->declareMod("stdprims","add2_n16");

  Type* inType = Int(n,IN);
  Type* treeType = Record({{"in",Array(inType,4)},{"out",Flip(inType)}});
  Module* addTree = c->defineModule("AddTree"+to_string(n),treeType);
  Wireable* iface = addTree->getInterface();
  Wireable* add_00 = addTree->addInstance("add00",addnGen,paramGen(n));
  Wireable* add_01 = addTree->addInstance("add01",addnGen,paramGen(n));
  Wireable* add_1 = addTree->addInstance("add1",addnMod);
  
  Connect(iface->sel("in")->sel(0),add_00->sel("inA"));
  Connect(iface->sel("in")->sel(1),add_00->sel("inB"));
  Connect(iface->sel("in")->sel(2),add_01->sel("inA"));
  Connect(iface->sel("in")->sel(3),add_01->sel("inB"));
  
  Connect(add_00->sel("out"),add_1->sel("inA"));
  Connect(add_01->sel("out"),add_1->sel("inA"));
  
  Connect(add_1->sel("out"),iface->sel("out"));

  return addTree;
}


int main() {
  CoreIRContext* c = newContext();
  
  cout << "Creating a 4->1 tree adder\n";
  Module* addtree16 = AddTree(c,16);
  addtree16->print();
  
  registerStdPrims(c,"stdprims");
  
  compile2Verilog(addtree16);
  
  addtree16->print();
  
  deleteContext(c);
  return 0;
}



