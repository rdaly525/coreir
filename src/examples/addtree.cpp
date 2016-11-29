#include "magmair.hpp"
#include <map>
#include <string>


MagmaIR* m = newMagmaIR();

// Creates an n-bit adder
Primitive* Adder(uint n) {
  Type* inType = Int(n,IN);
  Type* outType = Flip(inType);
  RecordType* rec = Record({{"inA",inType},{"inB",inType},{"out",outType}});
  cout << rec->_string() << endl;
  return m->newPrimitive("Add"+to_string(n),rec);
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
  Module* addTree = m->newModule("AddTree"+to_string(n),treeType);
  Wireable* iface = addTree->getInterface();
  Wireable* add_00 = addTree->newInstance("add00",addn);
  Wireable* add_01 = addTree->newInstance("add01",addn);
  Wireable* add_1 = addTree->newInstance("add1",addn);
  
  Connect(iface->sel("in")->sel(0),add_00->sel("inA"));
  Connect(iface->sel("in")->sel(1),add_00->sel("inB"));
  Connect(iface->sel("in")->sel(2),add_01->sel("inA"));
  Connect(iface->sel("in")->sel(3),add_01->sel("inB"));
  
  Connect(add_00->sel("out"),add_1->sel("inA"));
  Connect(add_01->sel("out"),add_1->sel("inB"));
  
  Connect(add_1->sel("out"),iface->sel("out"));
  return addTree;
}


int main() {
  //m = newMagmaIR();
  cout << "Creating a 4->1 tree adder\n";
  Circuit* addtree16 = AddTree(16);
  addtree16->print();
  Validate(addtree16);
  
  
  deleteMagmaIR(m);
  return 0;
}



