#include "coreir.h"
#include "assert.h"

int main() {
  C_CoreIRContext* c = C_newContext();
  //C_print(c);
  C_deleteContext(c);
  return 0;
}
