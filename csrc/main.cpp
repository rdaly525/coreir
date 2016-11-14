#include "magmair.hpp"
#include <map>
#include <string>

// Creates an n-bit adder
Primitive* Adder(uint n) {
  Type* inType = Int(n,IN);
  Type* outType = Flip(inType);
  return new Primitive("Add"+to_string(n),Record({{"inA",inType},{"inB",inType},{"out",outType}}));
}

// Creates a 4->1 add reduce tree
// in[0] - (+) - (+) - out
// in[1] /     /
// in[2] - (+) 
// in[3] / 
Module* AddTree(uint n) {
  Circuit* addn = Adder(n);
  Type* inType = Sel(getType(addn),"inA");
  Type* treeType = Record({{"in",Array(inType,4)},{"out",Flip(inType)}});
  Module* addTree = new Module("AddTree"+to_string(n),treeType);
  WireBundle* iface = addTree->getInterface();
  WireBundle* add_00 = addTree->newInstance("add00",addn);
  WireBundle* add_01 = addTree->newInstance("add01",addn);
  WireBundle* add_1 = addTree->newInstance("add1",addn);
  
  Connect(iface->sel("in")->idx(0),add_00->sel("inA"));
  Connect(iface->sel("in")->idx(1),add_00->sel("inB"));
  Connect(iface->sel("in")->idx(2),add_01->sel("inA"));
  Connect(iface->sel("in")->idx(3),add_01->sel("inB"));
  
  Connect(add_00->sel("out"),add_1->sel("inA"));
  Connect(add_01->sel("out"),add_1->sel("inB"));
  
  Connect(add_1->sel("out"),iface->sel("out"));
  return addTree;
}


int main() {

  cout << "Creating a 4->1 tree adder\n";
  Circuit* addtree16 = AddTree(16);
  addtree16->print();

  return 0;
}



