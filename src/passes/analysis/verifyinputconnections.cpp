#include "coreir.h"
#include "coreir/passes/analysis/verifyinputconnections.h"

using namespace std;
using namespace CoreIR;

namespace {
//True is error
//False is no error
bool checkTypes(Wireable* a, Wireable* b) {
  Context* c = a->getContext();
  Type* ta = a->getType();
  Type* tb = b->getType();
  //TODO This might not be valid if:
  //  2 outputs are connected to the same input
  //  an inout is connected to an input (good!)
  //  an inout is connected to an output (bad!)
  
  if (ta == c->Flip(tb) ) return false;
  
  Error e;
  e.message("Cannot wire together");
  e.message("  " + a->toString() + " : " + a->getType()->toString());
  e.message("  " + b->toString() + " : " + b->getType()->toString());
  c->error(e);
  return true;
}

//Checks if anything is a connected input. If so it is an error
//True is error
//False is no error
bool checkInputConnected(Wireable* w, Error* e) {
  if (!w->getType()->hasInput()) return false;
  
  // Assume this type is an input
  if (w->getConnectedWireables().size() > 0) {
    for (auto other : w->getConnectedWireables() )
      e->message("  " + w->toString() + " : " +  w->getType()->toString() + " <== " + other->toString() );
    return true;
  }
  bool err = false;
  for (auto it : w->getSelects()) {
    err |= checkInputConnected(it.second,e);
  }
  return err;
}

//TODO do stuff in numwires==1 even if errors on numwirew>1
//Checks if multiple thigns are connected to an input. If so an error
//True is error
//false is no error
bool checkInputOutputs(Wireable* w, Error* e) {
  assert(w);
  if (!w->getType()->hasInput()) return false;
  int numwires = w->getConnectedWireables().size();
  bool err = false;
  if (numwires > 1) {
    for (auto other : w->getConnectedWireables() )
      e->message("  " + w->toString() + " : " + w->getType()->toString() + " <== " + other->toString() );
    return true;
  }
  else if (numwires==0 ) {
    for ( auto it : w->getSelects()) {
      err |= checkInputOutputs(it.second,e);
    }
  }
  else if (numwires==1) {
    // Check if any children is an input and connected
    for ( auto it : w->getSelects()) {
      if(checkInputConnected(it.second,e)) {
        err = true;
        for (auto other : w->getConnectedWireables() )
          e->message("  " + w->toString() + " : " + w->getType()->toString() + " <== " + other->toString() );
      }
    }
  }
  else {
    assert(false);
  }
  return err;
}

}

string Passes::VerifyInputConnections::ID = "verifyinputconnections";
bool Passes::VerifyInputConnections::runOnModule(Module* m) {
  if (!m->hasDef()) return false;
  ModuleDef* mdef = m->getDef();
  Context* c = this->getContext();
  
  bool err = false;
  // Check for type compatability of every connection
  for (auto connection : mdef->getConnections() ) {
    err |= checkTypes(connection.first,connection.second);
  }
  
  //Check if an input is connected to multiple outputs
  vector<Wireable*> work;
  work.push_back(mdef->getInterface());
  for (auto instmap : mdef->getInstances() ) {
    ASSERT(instmap.second,"Bad instance!: " + instmap.first);
    work.push_back(instmap.second);
  }
  for (auto w : work) {
    Error e;
    e.message("Cannot connect multiple outputs to an inputs");
    e.message("In Module: " + m->getName());
    if (checkInputOutputs(w,&e)) {
      err = true;
      c->error(e);
    }
  }
  if (err) c->die();
  return false;
}
