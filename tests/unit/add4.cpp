#include "add4.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  uint n = 32;

  // New context
  Context* c = newContext();

  Module* add4 = create_adder(c, n);
  add4->print();
  deleteContext(c);

  return 0;
}
