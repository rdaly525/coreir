
#include "coreir/ir/directedview.h"
#include "coreir/ir/types.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/module.h"
#include "coreir/ir/moduledef.h"

using namespace std;
using namespace CoreIR;

DirectedConnection::DirectedConnection(Connection& c) : c(c) {
  Wireable* wa = c.first;
  Wireable* wb = c.second;
  //Confirm that one is definitely only inputs and one is only outputs
  Type* ta = wa->getType();
  Type* tb = wb->getType();
  assert(!ta->isUnknown() && !ta->isMixed());
  assert(!tb->isUnknown() && !tb->isMixed());
  if (ta->isInput()) {
    assert(tb->isOutput());
    src = wb;
    snk = wa;
  }
  else {
    assert(ta->isOutput() && tb->isInput());
    src = wa;
    snk = wb;
  }
}

Context* DirectedConnection::getContext() {
    // assumes the parent connection has wireables with the same context
    assert(c.first->getContext() == c.second->getContext());
    return c.first->getContext();
}
SelectPath DirectedConnection::getSrc() { return src->getSelectPath();}
SelectPath DirectedConnection::getSnk() { return snk->getSelectPath();}
ConstSelectPath DirectedConnection::getConstSrc() { return src->getConstSelectPath();}
ConstSelectPath DirectedConnection::getConstSnk() { return snk->getConstSelectPath();}

DirectedModule::DirectedModule(Module* m) : m(m) {
  assert(m->hasDef() && "Does not have def!");
  std::map<string,DirectedConnections> ins;
  std::map<string,DirectedConnections> outs;
  for (auto con : m->getDef()->getConnections()) {
    DirectedConnection* dcon = new DirectedConnection(con);
    connections.push_back(dcon);
    ins[dcon->getSnk()[0]].push_back(dcon);
    outs[dcon->getSrc()[0]].push_back(dcon);
  }
  for (auto inst : m->getDef()->getInstances()) {
    string selstr = inst.first;
    insts.push_back(new DirectedInstance(inst.second,ins[selstr],outs[selstr]));
  }
  inputs = outs["self"];
  outputs = ins["self"];
}

DirectedModule::~DirectedModule() {
    for (auto it : connections) delete it;
    for (auto it : insts) delete it;
}

Context* DirectedModule::getContext() { return m->getContext(); }

Wireable* DirectedModule::sel(SelectPath path) {
  return m->getDef()->sel(path);
}

  Instance* i;
  
  //Input edges to this module
  DirectedConnections inputs;

  //Output edges from this module
  DirectedConnections outputs;

DirectedInstance::DirectedInstance(Instance* i, DirectedConnections inputs, DirectedConnections outputs) : i(i), inputs(inputs), outputs(outputs) {}

Context* DirectedInstance::getContext() { return i->getContext(); }
