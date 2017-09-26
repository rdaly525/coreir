#include "coreir.h"
#include "coreir/passes/analysis/createmodinstancemap.h"

using namespace CoreIR;
using namespace std;

std::string Passes::CreateModInstanceMap::ID = "createmodinstancemap";
bool Passes::CreateModInstanceMap::runOnModule(Module* m) {
  InstanceMapType imap;
  for (auto instmap : m->getDef()->getInstances()) {
    Instantiable* i = instmap.second->getInstantiableRef();
    imap[i].insert(instmap.second);
  }
  this->modInstanceMap[m] = imap;
  return false;
}
