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
    CreateInstanceMap() : ModulePass(ID,"Create Instance Map",true) {}
    bool runOnModule(Module* ns) override;
    void releaseMemory() override {
      modInstanceMap.clear();
      genInstanceMap.clear();
    }
    std::set<Instance*> getModInstances(Module* m) {
      ASSERT(modInstanceMap.count(m),m->getRefName() + " has no instances!");
      return modInstanceMap[m];
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
