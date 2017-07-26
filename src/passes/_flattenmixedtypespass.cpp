



//vector<SelectPath> getListOfMixed(Type* t)


//This should remove any MixedTypes 
//This should also connect to only bits or Arrays of bits
class FlattenMixedTypesPass : public InstanceGraphPass {
  public :
    FlattenMixedTypesPass() : InstanceGraphPass() {}
    bool runOnNode(InstanceGraphNode& node) {
      //No need to change type of instance. Just disconnect any mixed types and reconnect a level of hierarchy down (recursively)
      Type* t = node->getInstantiable()->getType();
      vector<SelectPath> paths = getListOfMixed(t);
      for (auto inst : node->getInstances() ) {
        for (auto path : paths) {
          bool err = false;
          Wireable* w = carefulSel(inst,path,&err);
          if (!err) {
            assert(s->getType()->isMixed())
            //This is a mixed type. Connect all wires down one level
            auto connected = s->getConnectedWireables();
            
            //Then disconnect all the current connected Wireables
          }
        }
      }
    }
}


