#include "coreir.hpp"
//#include <string>

#include <fstream>
#include "stdprims.hpp"

int main() {
  uint n = 32;
  CoreIRContext* c = new CoreIRContext();
  
  //Declare add2 module (with 32 bits)
  Instantiable* add2 = c->declareMod("stdprims","add2_"+to_string(n));

  // Define Add4 Module
  Type* add4Type = Record({{"in",Array(Int(n,IN),4)},{"out",Int(n,OUT)}});
  ModuleDef* add4 = new ModuleDef("Add4",add4Type);
    Wireable* iface = add4->getInterface();
    Wireable* add_00 = add4->addInstance("add00",add2);
    Wireable* add_01 = add4->addInstance("add01",add2);
    Wireable* add_1 = add4->addInstance("add1",add2);
    
    add4->wire(iface->sel("in")->sel(0),add_00->sel("in0"));
    add4->wire(iface->sel("in")->sel(1),add_00->sel("in1"));
    add4->wire(iface->sel("in")->sel(2),add_01->sel("in0"));
    add4->wire(iface->sel("in")->sel(3),add_01->sel("in1"));

    add4->wire(add_00->sel("out"),add_1->sel("in0"));
    add4->wire(add_01->sel("out"),add_1->sel("in1"));

    add4->wire(add_1->sel("out"),iface->sel("out"));
  // End Define Add4 Module
  add4->print();

  //Add Def to global
  c->getGlobal()->addModuleDef(add4);
    
  //Link stdprim library
  NameSpace* prims = registerStdPrims(c,"stdprims");
  prims->print();
  fstream f;
  f.open("add4.v",fstream::out);
  assert(f.is_open());
  compile(c,add4,&f);
  f.close();

  deleteContext(c);
  
  return 0;
}
