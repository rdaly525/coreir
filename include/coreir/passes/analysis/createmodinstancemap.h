#ifndef CREATEMODINSTANCEMAP_HPP_
#define CREATEMODINSTANCEMAP_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateModInstanceMap : public ModulePass {
  public:
    //Map from Instantiables to a list of instances
    typedef std::unordered_map<Instantiable*,std::unordered_set<Instance*>> InstanceMapType;
  private:
    std::unordered_map<Module*,InstanceMapType> modInstanceMap;
  public :
    static std::string ID;
    CreateModInstanceMap() : ModulePass(ID,"Create Instance Map",true) {}
    bool runOnModule(Module* ns) override;
    void releaseMemory() override {
      modInstanceMap.clear();
    }
    InstanceMapType getInstanceMap(Module* m) {
      ASSERT(modInstanceMap.count(m),"Missing Module!" + m->getName());
      return modInstanceMap[m];
    }
};

}
}
#endif
