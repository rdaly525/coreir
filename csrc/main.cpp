#include "magmair.hpp"
#include <map>
#include <string>
//void port(string name, uint width,

//Implement or(a[8] + b[8] )
/*
int main(int argv[], int argn) {
  
  MAG mod = mag.new();
  IFACE pa = mag.port("a",8,true);
  PORT pb = mag.port("b",8,true);
  PORT pc = mag.port("c",1,false);
  RECORD rec = mag.record([pa,pb,pc])

}
*/

int main() {
  IntType* int7 = Int(7,IN);
  ArrayType* array5 = Array(int7,5);
  map<string,Type*> m = {{"b",int7},{"c",array5}};
  RecordType* r = Record(m);
  r->print();

  Module* modA = new Module("A",false,r);
  Module* modB = new Module("B",true,int7);
  Module* modC = new Module("C",true,array5);
  Instance* b_inst = modA->newInstance("b_inst",modB);
  Instance* c_inst = modA->newInstance("c_inst",modC);
  Interface* a_iface = modA->getInterface();
  WireBundle* s = a_iface->sel("c");
  Index* s2 = s->idx(2);
  Connect(a_iface->sel("b"),b_inst);
  Connect(s2,b_inst);
  modA->print();

  delete modA;
  delete modB;
  delete modC;

  return 0;
}

