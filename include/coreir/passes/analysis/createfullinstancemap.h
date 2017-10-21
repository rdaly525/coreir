#ifndef CREATEINSTANCEMAP_HPP_
#define CREATEINSTANCEMAP_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateInstanceMap : public ModulePass {
  //Map from Instantiables to a list of instances
  std::map<Instantiable*,std::set<Instance*>> modInstanceMap;
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
    std::set<Instance*> getModuleInstances(Instantiable* i) {
      ASSERT(this->hasInstances(i),i->getRefName() + " has no instances!");
      return instanceMap[i];
    }
    std::map<Instantiable*,std::set<Instance*>>& getModInstanceMap() {
      return instanceMap;
    }
};

}
}
#endif
