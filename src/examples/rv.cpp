#include "magmair.hpp"
#include <map>
#include <string>

MagmaIR* m = newMagmaIR();

Type* RV(Type* dataType) {
  return Record({{"data",dataType},{"valid",Int(1)},{"ready",Flip(Int(1))}});
}




int main() {

  Type* rv16 = RV(Int(16));
  Primitive* binop= m->newPrimitive("binop",Record({{"inA", rv16},{"inB", rv16},{"out",Flip(rv16)}}));
  Primitive* unop= m->newPrimitive("unop",Record({{"in",rv16},{"out",Flip(rv16)}}));


  Module* fused = m->newModule("fused",getType(binop));
  Wireable* iface = fused->getInterface();
  Wireable* binopInst = fused->newInstance("bop",binop);
  Wireable* unopInst = fused->newInstance("uop",unop);

  Connect(iface->sel("inA"),binopInst->sel("inA"));
  Connect(iface->sel("inB"),binopInst->sel("inB"));
  Connect(binopInst->sel("out"),unopInst->sel("in"));
  Connect(unopInst->sel("out"),iface->sel("out"));
  fused->print();
  Validate(fused);
  
  deleteMagmaIR(m);
  return 0;
}



