#include "coreir.h"
#include "coreir-lib/stdlib.h"

using namespace CoreIR;

int main() {
  
  // New context
  Context* c = newContext();
  
  Params params({{"width",AINT},{"en",ABOOL}});
  auto vt = new VTRecord();
  auto insel = new VSelect<Type*>(
    new VEq<int>(new VArg<int>("width"), new VConst<int>(1)),
    new VTBitIn(),
    new VTArray(new VArg<int>("width"),new VTBitIn())
  );
  auto outsel = new VSelect<Type*>(
    new VEq<int>(new VArg<int>("width"), new VConst<int>(1)),
    new VTBit(),
    new VTArray(new VArg<int>("width"),new VTBit())
  );

  vt->addField("in",insel,new VConst<bool>(true));
  vt->addField("out",outsel,new VConst<bool>(true));
  vt->addField("en",new VTBitIn(),new VArg<bool>("en"));
  TypeGen* tg = new TypeGenLang(c->getGlobal(),"Tester",params,vt);
  tg->getType({{"width",c->argInt(7)},{"en",c->argBool(true)}})->print();
  tg->getType({{"width",c->argInt(34)},{"en",c->argBool(false)}})->print();
  tg->getType({{"width",c->argInt(1)},{"en",c->argBool(true)}})->print();
  deleteContext(c);
  
  return 0;
}
