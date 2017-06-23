#include "coreir-pass/passes.h"

namespace CoreIR {

class MatchAndReplacePass : public ModulePass {
  public:
    typedef std::function<Args(const Instance*)> ConfigArgFunType;
  private:
    Module* pattern;
    Module* replacement;
    std::function<Args(const Instance*)> getConfigArgs;
  public:
    explicit MatchAndReplacePass(Module* pattern, Module* replacement, Args configargs=Args()) : ModulePass(), pattern(pattern), replacement(replacement) {
      this->getConfigArgs = [&configargs](const Instance* matched) {
        return configargs;
      };
    }
    explicit MatchAndReplacePass(Module* pattern, Module* replacement,ConfigArgFunType getConfigArgs) : ModulePass(), pattern(pattern), replacement(replacement) {}
    bool runOnModule(Module* m);

};

}
