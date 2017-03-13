#include "coreir.h"
#include "assert.h"
#include "stdio.h"

int main() {
  COREContext* c = CORENewContext();
  COREType* bitIn = COREBitIn(c);
  CORENamespace* ns = COREGetGlobal(c);
  
  COREModule* m = CORENewModule(ns,"Add8",bitIn);
  bool err = false;
  CORESaveModule(m,"simple.json",&err);
  if (err) {
    printf("Cannot open simple.json\n");
    return 1;
  }
  COREPrintModule(m);
  
  COREDeleteContext(c);
  return 0;
}
