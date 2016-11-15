#include "magmair.hpp"
#include <map>
#include <string>

// Creates an n-bit adder primitive
Primitive* Adder(uint n) {
  Type* inType = Int(n,IN);
  Type* outType = Flip(inType);
  Type* addType = Record({{"inA",inType},{"inB",inType},{"out",outType}});
  return new Primitive("Add"+to_string(n),addType);
}

// Creates a 4->1 add reduce tree but adds in[2] twice
// in[0] - - (+) - (+) - out
// in[1] - /     /
// in[2] - - (+) 
//       \ / 
Module* AddTree(uint n) {
  Circuit* addn = Adder(n);
  Type* inType = Sel(getType(addn),"inA");
  Type* treeType = Record({{"in",Array(inType,3)},{"out",Flip(inType)}});
  Module* addTree = new Module("AddTree"+to_string(n),treeType);
  Wireable* iface = addTree->getInterface();
  Wireable* add_00 = addTree->newInstance("add00",addn);
  Wireable* add_01 = addTree->newInstance("add01",addn);
  Wireable* add_1 = addTree->newInstance("add1",addn);
  
  Connect(iface->sel("in")->sel(0),add_00->sel("inA"));
  Connect(iface->sel("in")->sel(1),add_00->sel("inB"));
  Connect(iface->sel("in")->sel(2),add_01->sel("inA"));
  Connect(iface->sel("in")->sel(2),add_01->sel("inB"));
  
  Connect(add_00->sel("out"),add_1->sel("inA"));
  Connect(add_01->sel("out"),add_1->sel("inB"));
  
  Connect(add_1->sel("out"),iface->sel("out"));
  
  //Connect(add_00->sel("out"),iface->sel("out"));

  return addTree;
}


int main() {
  cout << "Creating a 4->1 tree adder\n";
  Circuit* addtree16 = AddTree(16);
  Validate(addtree16);
  addtree16->print();

  return 0;
}

