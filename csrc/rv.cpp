#include "magmair.hpp"
#include <map>
#include <string>


Type* RV(Type* dataType) {
  return Record({{"data",dataType},{"valid",Int(1,IN)},{"ready",Int(1,OUT)}});
}

int main() {

  Type* rv16 = RV(Int(16,IN));
  Primitive* binop= new Primitive("binop",Record({{"inA", rv16},{"inB", rv16},{"out",Flip(rv16)}}));
  Primitive* unop= new Primitive("unop",Record({{"in",rv16},{"out",Flip(rv16)}}));


  Module* fused = new Module("fused",getType(binop));
  WireBundle* iface = fused->getInterface();
  WireBundle* binopInst = fused->newInstance("bop",binop);
  WireBundle* unopInst = fused->newInstance("uop",unop);

  Connect(iface->sel("inA"),binopInst->sel("inA"));
  Connect(iface->sel("inB"),binopInst->sel("inB"));
  Connect(binopInst->sel("out"),unopInst->sel("in"));
  Connect(unopInst->sel("out"),iface->sel("out"));
  fused->print();

  return 0;
}



