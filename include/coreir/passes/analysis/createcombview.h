#ifndef COREIR_CREATECOMBVIEW_HPP_
#define COREIR_CREATECOMBVIEW_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CreateCombView : public InstanceGraphPass {
  public:
    struct Comb {
      std::set<SelectPath> inputs;
      std::set<SelectPath> outputs;
    };

    struct Output {
      std::set<Wireable*> states;
      std::set<Wireable*> inputs;
    };

    struct Input {
      std::set<Wireable*> states;
      std::set<Wireable*> outputs; //Unused for now
    };

  private:

    std::map<Module*,std::set<SelectPath>> srcs;
    std::map<Module*,std::set<SelectPath>> snks;
    std::map<Module*,Comb> combs;

  public :
    static std::string ID;
    CreateCombView() : InstanceGraphPass(ID,"create comb view datastructures",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    bool hasSrc(Module* m) { 
      return (srcs.count(m) > 0) && srcs[m].size() > 0;
    }
    bool hasSnk(Module* m) { 
      return (snks.count(m) > 0) && snks[m].size() > 0;
    }
    bool hasComb(Module* m) {
      return (combs.count(m) > 0) && (combs[m].inputs.size()>0 || combs[m].outputs.size()>0);
    }

    std::set<SelectPath>& getSrc(Module* m) {
      return srcs[m];
    }
    std::set<SelectPath>& getSnk(Module* m) {
      return snks[m];
    }
    Comb& getComb(Module* m) {
      return combs[m];
    }

  private:
    void setupCoreir(Module* m);
    void setupCorebit(Module* m);
    void traverseOut2In(Wireable* curin, Wireable* out, std::map<Wireable*,Output*>& outputInfo, std::map<Wireable*,Input*>& inputInfo);

};

}
}
#endif
