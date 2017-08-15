

//This should have already run:
//runAllGenerators
//flattenMixedTypes
class FlattenTypesPass : public InstanceGraphPass {
  
  public :
    FlattenTypesPass() : InstanceGraphPass() {}
    bool runOnNode(InstanceGraphNode& node) {
      
      //TODO fill in this path2str
      unorderd_map<SelectPath,string> path2str;
      
      for (auto pmap : path2str) {
        node.appendToRecord(pmap.second,TODOtype);
      }

      //Add all instances and internal interface to list
      vector<Wireable*> ws(node.getInstances());
      if (auto m = dyn_cast<Module>(node.getInstantiable()) && m->hasDef()) {
        ws.push_back(m->getDef()->getInterface());
      }
      for (auto inst : node.getInstances()) {
        auto pt = addPassthrough("_pt",inst);
        //Disconnect passthrough from instance
        pt->sel("in")->disconnect();

        //Reconnect everything to the new port name
        for (auto pmap : path2str) {
          Wireable* a = pt->sel("in")->sel(pmap.first);
          inst->sel(pmap.second)->connect(a);
        }

        //inline passthrough
        inlineInstance(pt);
      }

      //Finally remove all connections
      for(auto  pmap : path2str) {
        node.detachFromRecord(pmap.first[0]);
      }

    }
}
