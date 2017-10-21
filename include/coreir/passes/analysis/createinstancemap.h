#ifndef CREATEINSTANCEMAP_HPP_
#define CREATEINSTANCEMAP_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateInstanceMap : public ModulePass {
  std::map<Module*,std::set<Instance*>> modInstanceMap;
  std::map<Generator*,std::set<Instance*>> genInstanceMap;
  public :
    static std::string ID;
    CreateFullInstanceMap() : ModulePass(ID,"Create Instance Map",true) {}
    bool runOnModule(Module* ns) override;
    void releaseMemory() override {
      instanceMap.clear();
    }
    std::set<Instance*> getModInstances(Module* m) {
      ASSERT(this->hasInstances(i),i->getRefName() + " has no instances!");
      return modInstanceMap[i];
    }
    std::map<Module*,std::set<Instance*>>& getModInstanceMap() {
      return modInstanceMap;
    }
    std::map<Generator*,std::set<Instance*>>& getGenInstanceMap() {
      return genInstanceMap;
    }
};

}
}
#endif
