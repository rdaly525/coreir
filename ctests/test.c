#include "coreir.h"
#include "assert.h"

int main() {
  COREContext* c = CORENewContext();
  COREType* bitIn = COREBitIn(c);
  COREType* array = COREArray(c,8,bitIn);
  
  COREPrintType(array);
  
  COREModule* m = CORELoadModule(c, "myfile.json");
  COREPrintModule(m);


  COREDeleteContext(c);
  return 0;
}
