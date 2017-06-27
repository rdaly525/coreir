#include "coreir-pass/passes.h"

namespace CoreIR {

class MatchAndReplacePass : public ModulePass {
  public:
    typedef std::function<Args(const std::vector<Instance*>&)> ConfigArgFun;
    typedef std::function<bool(const std::vector<Instance*>&)> MatchingCheckFun;
    typedef struct {
      Args configargs = Args(); //used if replacement is always a constant configargs
      std::vector<std::string> instanceKey; //Used for reference in following two functions
      MatchingCheckFun checkMatching = nullptr; //Checks if a matching pattern is really matching
      ConfigArgFun getConfigArgs = nullptr; //Calculates the configars based off the matching pattern
    } Opts;
      
  private:
    Module* pattern;
    Module* replacement;
    
    void verifyOpts(Opts opts);
    
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
    
    //Step 2 stuff



  public:
    explicit MatchAndReplacePass(Module* pattern, Module* replacement, Opts opts=Opts()) : ModulePass(), pattern(pattern), replacement(replacement), configargs(opts.configargs), getConfigArgs(opts.getConfigArgs), checkMatching(opts.checkMatching), instanceKey(opts.instanceKey) {
      this->verifyOpts(opts);
      this->preprocessPattern();
    }
    bool runOnModule(Module* m);

};

}
