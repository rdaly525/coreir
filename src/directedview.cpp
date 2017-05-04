
#include "dview.hpp"
#include "wireable.hpp"

using namespace CoreIR;

DirectedConnection::DirectedConnection(Connection& c) : c(c) {
  Wireable* wa = c.first;
  Wireable* wb = c.second;
  wa->toString();
  wb->toString();
  //Confirm that one is definitely only inputs and one is only outputs
}

DirectedModule::DirectedModule(Module* m) {

}

Wireable* DirectedModule::sel(SelectPath path) {

}

