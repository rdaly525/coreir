#include "coreir.h"
#include "assert.h"

int main() {
  COREContext* c = CORENewContext();
  COREType* bitIn = COREBitIn(c);
  CORENamespace* ns = COREGetGlobal(c);
  
  COREModule* m = CORENewModule(ns,"Add8",bitIn);
  COREPrintModule(m);
  
  printf("Trying to delete context\n");
  COREDeleteContext(c);
  return 0;
}
