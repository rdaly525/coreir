

class FlattenAllPass : public InstanceDAGPass {
  public :
    InlinePass() : InstanceDAGPass() {}
    bool runOnModule(Module* m) {
      bool changed = false;
      for (instmap : m->getInstances()) {
        instmap.second->inlineInstance();
        changed = true;
      }
      return changed;
    }
    bool runOnInstance(Instance* i) {
      return false;
    }
}
