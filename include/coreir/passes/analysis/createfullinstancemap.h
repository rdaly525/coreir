#ifndef CREATEFULLINSTANCEMAP_HPP_
#define CREATEFULLINSTANCEMAP_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateFullInstanceMap : public ModulePass {
  //Map from Instantiables to a list of instances
  unordered_map<Instantiable*,unordered_set<Instance*>> instanceMap;
  public :
    static std::string ID;
    CreateFullInstanceMap() : ModulePass(ID,"Create Instance Map",true) {}
    bool runOnModule(Module* ns) override;
    void releaseMemory() override {
      instanceMap.clear();
    }
    bool hasInstances(Instantiable* i) {
      return instanceMap.count(i) > 0;
    }
    unordered_set<Instance*> getInstances(Instantiable* i) {
      ASSERT(this->hasInstances(i),i->getRefName() + " has no instances!");
      return instanceMap[i];
    }
    unordered_map<Instantiable*,unordered_set<Instance*>>& getFullInstanceMap() {
      return instanceMap;
    }
};

}
}
#endif
