#include "magmair.hpp"
#include <map>
#include <string>


MagmaIR* m = newMagmaIR();
Primitive* regPrim(uint n) {
  Type* regType = Record({{"clk",Int(1,IN)},
                  {"D",Int(n,IN)},
                  {"Q",Int(n)}});
  return m->newPrimitive("Reg",regType);
}

int main() {

  uint n = 8;
  uint len = 6;
  Type* regArray6Type = Array(getType(regPrim(n)),len);
  Module* regArray6 = m->newModule("regArray6",regArray6Type);
  for (uint i=0; i<len; i++) {
    Instance* inst = regArray6->newInstance("reg"+to_string(i),regPrim(n));
    Connect(inst, regArray6->getInterface()->sel(i));
  }
  regArray6->print();
  Validate(regArray6);

  deleteMagmaIR(m);
  return 0;
}
