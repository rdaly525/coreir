#ifndef COREIR_LIBS_CPP_
#define COREIR_LIBS_CPP_

TODO
guards

string WireableEnum2Str(WireableEnum wb) {
  switch(wb) {
    case IFACE: return "Interface";
    case INST: return "Instance";
    case SEL: return "Select";
  }
  assert(false);
}


bool Validate(Circuit* c) {

  // Circuit is valid if its interface and all its instances are _wired
  //TODO
  bool valid = true;
  Module* mod = (Module*) c;
  if (!mod->getInterface()->checkWired()) {
    cout << "Inteface is Not fully connected!\n";
    return false;
  }
  vector<Instance*> insts = mod->getInstances();
  vector<Instance*>::iterator it;
  for(it=insts.begin(); it!=insts.end(); ++it) {
    if (!(*it)->checkWired() ) {
      cout << "Instance: " << (*it)->_string() << " is not fully connected\n";
      valid = false;
    }
  }
  cout << "You have a valid Module!\n";
  return valid;
}

#endif //COREIR_LIBS_CPP_
