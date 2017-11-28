#ifndef COREIR_CREATECOMBVIEW_HPP_
#define COREIR_CREATECOMBVIEW_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateCombView : public InstanceGraphPass {
  std::map<Module*,std::set<SelectPath>> srcs;
  std::map<Module*,std::set<SelectPath>> snks;
  std::map<Module*,std::pair<std::set<SelectPath>,std::set<SelectPath>> combs;

  public :
    static std::string ID;
    CreateCombView() : InstanceGraphPass(ID,"create comb view datastructures",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    
    bool hasSrc(Module* m);
    bool hasSnk(Module* m);
    bool hasComb(Module* m);

    std::set<std::string> getSrc(Module* m);
    std::set<std::string> getSnk(Module* m);
    std::pair<std::set<std::string>,std::set<std::string>> getComb(Module* m);

};

}
}
#endif
