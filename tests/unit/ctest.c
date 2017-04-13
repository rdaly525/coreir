#include "coreir.h"
#include "assert.h"
#include "stdio.h"
#include "stdlib.h"

void print(char* a) {
  printf("%s",a); printf("\n"); fflush(stdout);
}

int main() {
  COREContext* c = CORENewContext();
  bool err = false;
  
  char** rkeys = malloc(2*sizeof(char*));
  rkeys[0] = "in";
  rkeys[1] = "out";
  COREType** rvalues = malloc(2*sizeof(COREType*));
  rvalues[0] = COREBitIn(c);
  rvalues[1] = COREBitOut(c);

  void* recordparams = CORENewMap(c,rkeys,rvalues,2,STR2TYPE_ORDEREDMAP);

  COREType* lut4type = CORERecord(c,recordparams);
  CORENamespace* ns = COREGetGlobal(c);
  char** cpkeys = malloc(2*sizeof(char*));
  cpkeys[0] = "in";
  cpkeys[1] = "out";
  int** cpparams = malloc(2*sizeof(int*));
  cpparams[0] = 0;
  cpparams[1] = 0;

  void* cp = CORENewMap(c,cpkeys,cpparams,2,STR2PARAM_MAP);

  COREModule* lut4 = CORENewModule(ns,"LUT4",lut4type,cp);
  

  COREModule* m = CORENewModule(ns,"Main",COREBitIn(c),NULL);

  COREModuleDef* mdef = COREModuleNewDef(m);

  char** ckeys = malloc(2*sizeof(char*));
  ckeys[0] = "in";
  ckeys[1] = "out";
  COREArg** cargs = malloc(2*sizeof(COREArg*));
  cargs[0] = COREInt2Arg(c,13);
  cargs[1] = COREInt2Arg(c,13);

  void* config = CORENewMap(c,ckeys,cargs,2,STR2ARG_MAP);
  



  COREModuleDefAddModuleInstance(mdef, "ctop",lut4,config);

  COREModuleAddDef(m,mdef);

  COREPrintModule(m);


  CORESaveModule(m,"_simple.json",&err);
  if (err) {
    COREPrintErrors(c);
    printf("Cannot open _simple.json\n");
    return 1;
  }

  COREPrintModule(m);

  COREDeleteContext(c);
  c = CORENewContext(c);
  m = CORELoadModule(c,"_simple.json",&err);
  if (err) {
    COREPrintErrors(c);
    printf("Cannot load _simple.json\n");
    return 1;
  }
  printf("Loaded Module!\n");
  COREPrintModule(m);

  return 0;
}
