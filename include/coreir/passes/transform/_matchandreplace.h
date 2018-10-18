#ifndef MATCHANDREPLACE_HPP_
#define MATCHANDREPLACE_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {


class MatchAndReplacePass : public ModulePass {
  std::vector<std::string> instanceKey; //Used for reference in following two functions

  //Checks if a matching pattern is really matching
  virtual bool checkMatching(const std::vector<Instance*>&) {
    return true;
  }
  
  //Calculates the modargs based off the matching pattern
  virtual Values getModArgs(const std::vector<Instance*>&) {
    return Values();
  }
  
  //Calculates the modargs based off the matching pattern
  virtual Values getGenArgs(const std::vector<Instance*>&) {
    return Values();
  }

  MatchAndReplaceOpts() {}
    };

    Module* pattern;
    Instantiable* replacement;

    void verifyOpts(MatchAndReplaceOpts opts);

    Values genargs;
    Values modargs;
    ModArgFun getModArgs; //Can be null
    MatchingCheckFun checkMatching; //can be null

    //Step 1 stuff

    //pattern data structures
    std::vector<std::string> instanceKey;

    //TODO explain this data type
    typedef std::vector<std::unordered_map<SelectPath,std::vector<std::pair<SelectPath,uint>>>> InternalConnections;
    InternalConnections inCons;

    //TODO explain this too
    typedef std::vector<std::vector<std::pair<SelectPath,SelectPath>>> ExternalConnections;
    ExternalConnections exCons;

    void preprocessPattern();


  public:
    explicit MatchAndReplace(std::string name, Module* pattern, Instantiable* replacement, Opts opts=Opts()) : ModulePass(name,"Matches a module and replaces it"), pattern(pattern), replacement(replacement), genargs(opts.genargs), modargs(opts.modargs), getModArgs(opts.getModArgs), checkMatching(opts.checkMatching), instanceKey(opts.instanceKey) {
      mergeValues(genargs, dyn_cast<Generator>(replacement)->getDefaultGenArgs());
      this->verifyOpts(opts);
      this->preprocessPattern();
    }
    void setAnalysisInfo() override {
      addDependency("createmodinstancemap");
    }
    bool runOnModule(Module* m) override;

};

}
}

#endif
