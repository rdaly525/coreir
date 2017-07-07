
class FlattenMixedTypesPass : public InstanceDAGPass {
  public :
    typedef std::function<std::string(SelectPath)> SelectPathConcat;
  private:
    SelectPathConcat concatFun;
    FlattenMixedTypesPass(SelectPathConcat fun) : InstanceDAGPass(), concatFun(concatFun) {}
    FlattenMixedTypesPass() : InstanceDAGPass() {
      concatFun = [](SelectPath path) {
        string ret = "";
        for (auto selstr : path) {
          ret = ret + "_" + selstr;
        }
        return ret;
      };
    bool runOnModule(Module* m) {
    
    }
    bool runOnInstanceNode(Instance* i) {
    
    }
}


