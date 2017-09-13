#ifndef MATCHANDREPLACE_HPP_
#define MATCHANDREPLACE_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class MatchAndReplace : public ModulePass {
  public:
    
    typedef std::function<Args(const std::vector<Instance*>&)> ConfigArgFun;
    typedef std::function<bool(const std::vector<Instance*>&)> MatchingCheckFun;
    struct Opts {
      Args configargs = Args(); //used if replacement is always a constant configargs
      Args genargs = Args(); // Used if replacement is a generator
      std::vector<std::string> instanceKey; //Used for reference in following two functions
      MatchingCheckFun checkMatching = nullptr; //Checks if a matching pattern is really matching
      ConfigArgFun getConfigArgs = nullptr; //Calculates the configars based off the matching pattern
      Opts() {}
    };
      
  private:
    Module* pattern;
    Instantiable* replacement;
    
    void verifyOpts(Opts opts);
    
    Args genargs;
    Args configargs;
    ConfigArgFun getConfigArgs; //Can be null
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
    explicit MatchAndReplace(std::string name, Module* pattern, Instantiable* replacement, Opts opts=Opts()) : ModulePass(name,"Matches a module and replaces it"), pattern(pattern), replacement(replacement), genargs(opts.genargs), configargs(opts.configargs), getConfigArgs(opts.getConfigArgs), checkMatching(opts.checkMatching), instanceKey(opts.instanceKey) {
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
