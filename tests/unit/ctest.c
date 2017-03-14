#include "coreir.h"
#include "assert.h"
#include "stdio.h"

int main() {
  COREContext* c = CORENewContext();
  COREType* bitIn = COREBitIn(c);
  CORENamespace* ns = COREGetGlobal(c);
  
  COREGenParams* cp = CORENewGenParams(c);
  COREGenParamsAddField(cp,"lut_table",COREGINT);
  COREModule* lut4 = CORENewModule(ns,"LUT4",bitIn,cp);
  
  printf("J1\n");
  COREModule* m = CORENewModule(ns,"Main",bitIn,NULL);
  printf("J2\n");

  COREModuleDef* mdef = COREModuleNewDef(m);

  COREGenArgs* config = CORENewGenArgs(c);
  COREGenArgsAddField(config,"lut_table",COREGInt(c,255));

  COREModuleDefAddModuleInstance(mdef, "lut0",lut4,config);
  COREModuleAddDef(m,mdef);

  bool err = false;
  CORESaveModule(m,"simple.json",&err);
  if (err) {
    COREPrintErrors(c);
    printf("Cannot open simple.json\n");
    return 1;
  }
  COREPrintModule(m);
  COREDeleteContext(c);
  c = CORENewContext(c);
  m = CORELoadModule(c,"simple.json",&err);
  if (err) {
    COREPrintErrors(c);
    printf("Cannot load simple.json\n");
    return 1;
  }
  printf("Loaded Module!\n");
  COREPrintModule(m);

  return 0;
}
