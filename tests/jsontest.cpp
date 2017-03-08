#include "context.hpp"
#include <cassert>
#include "passes.hpp"

#include <iostream>
#include <fstream>

int main() {
  Context* c = newContext();
  loadModule(c,"a.json");
  deleteContext(c);
  return 0;
}
