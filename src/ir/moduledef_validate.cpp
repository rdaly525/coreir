
#include "coreir/ir/moduledef.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/types.h"
#include "coreir/ir/error.h"

using namespace std;

namespace CoreIR {
//True is error
//False is no error
bool ModuleDef::checkTypes(Wireable* a, Wireable* b) {

  //cout << "Getting context of " << a->toString() << endl;
  Context* c = a->getContext();
  //cout << "Got context" << endl;

  Type* ta = a->getType();
  Type* tb = b->getType();
  //TODO This might not be valid if:
  //  2 outputs are connected to the same input

  //cout << "Got types" << endl;
  
  if (ta == c->Flip(tb) ) {
    //cout << "ta flipped" << endl;
    return false;
  }

  //cout << "Flipped types" << endl;
  
  Error e;
  e.message(a->getContainer()->getName() + ": Cannot wire together");
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

//Checks if multiple thigns are connected to an input. If so an error
//True is error
//false is no error
bool checkInputOutputs(Wireable* w, Error* e) {
  if (!w->getType()->hasInput()) {
    return false;
  }

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

//true is Error
//false is no error
bool ModuleDef::validate() {
  ModuleDef* mdef = this;
  Context* c = mdef->getModule()->getContext();
  
  bool err = false;
  // Check for type compatability of every connection
  for (auto connection : mdef->getConnections() ) {
    err |= checkTypes(connection.first,connection.second);
  }
  
  //Check if an input is connected to multiple outputs
  vector<Wireable*> work;
  work.push_back(mdef->getInterface());
  for (auto instmap : mdef->getInstances() ) {
    work.push_back(instmap.second);
  }
  for (auto w : work) {
    Error e;
    e.message("Cannot connect multiple outputs to an inputs");
    e.message("In Module: " + mdef->getModule()->getName());
    if (checkInputOutputs(w,&e)) {
      err = true;
      c->error(e);
    }
  }
  return err;
}




}//CoreIR namespace
