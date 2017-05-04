
#include "directedview.hpp"
#include "wireable.hpp"

using namespace CoreIR;

DirectedConnection::DirectedConnection(Connection& c) : c(c) {
  Wireable* wa = c.first;
  Wireable* wb = c.second;
  wa->toString();
  wb->toString();
  //Confirm that one is definitely only inputs and one is only outputs
  Type* ta = wa->getType();
  Type* tb = wb->getType();
  assert(!ta->isUnknown() && !ta->isMixed());
  assert(!tb->isUnknown() && !tb->isMixed());
  if (ta->isInput()) {
    assert(tb->isOutput());
    src = wb->getSelectPath();
    snk = wa->getSelectPath();
  }
  else {
    assert(ta->isOutput() && tb->isInput());
    src = wa->getSelectPath();
    snk = wb->getSelectPath();
  }
}

DirectedModule::DirectedModule(Module* m) : m(m) {
  assert(m->hasDef() && "Does not have def!");
  std::map<string,DirectedConnections> ins;
  std::map<string,DirectedConnections> outs;
  for (auto con : m->getDef()->getConnections()) {
    DirectedConnection dcon(con);
    connections.push_back(dcon);
    ins[dcon.getSnk()[0]].push_back(dcon);
    outs[dcon.getSrc()[0]].push_back(dcon);
  }
  for (auto inst : m->getDef()->getInstances()) {
    string selstr = inst.first;
    insts.push_back(DirectedInstance(inst.second,ins[selstr],outs[selstr]));
  }
}

Wireable* DirectedModule::sel(SelectPath path) {
  return m->getDef()->sel(path);
}

  Instance* i;
  
  //Input edges to this module
  DirectedConnections inputs;

  //Output edges from this module
  DirectedConnections outputs;

DirectedInstance::DirectedInstance(Instance* i, DirectedConnections inputs, DirectedConnections outputs) : i(i), inputs(inputs), outputs(outputs) {}
