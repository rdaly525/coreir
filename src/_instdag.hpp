
// This for the culling stuff
//TODO finish this code
  /*
  //Generate a list of all dependencies by traversing instanceDAG
  unordered_set<SymbolRef> insts;
  unordered_set<SymbolRef> named;
  
  insts.insert(SymbolRef(m->getNamespace()->getName(),m->getName()));
  std::function<void(Module*)> traverse = [&insts,&named,&c,&traverse](Module* m)->void {
    for (auto i : m->getDef()->getInstances()) {
      Instantiable* iref = i.second->getInstRef();
      insts.insert(iref->getNamespace()->getName(),iref->getName());
      if (iref->isKind(MOD)) {
        traverse((Module*) iref);
      }
      Type* type = i.second->getType();
      if (type->isKind(NAMED)) {
        NamedType* namedtype = (NamedType*) type;
        named.insert(SymbolRef(namedtype->getNamespace()->getName(),namedtype->getName()));
      }
    }
  };
  traverse(m);
  
  for (auto nsname : depNamespaces) {
    cout << "writing namespaces!" << endl;
    j["namespaces"][nsname] = c->getNamespace(nsname)->toJson();
  }
  */

/*
template<class T>
class DAGnode {
  //Provides a mapping from {ns,name} to counts of that instance
  unordered_map<T,uint> insts;
  public:
    InstanceDAG() {}
    void insert(T key) {
      insts[key] +=1;
    }
    void remove(T key) {
      if (insts.count(key) <=1) {
        insts.erase(key);
      }
      else {
        insts[key] -=1 ;
      }
    }
    vector<T> get() {
      vector<T> keys;
      for (auto k : insts) keys.push_back(k.first);
      return keys;
    }
};
*/
class InstanceDAG {
  //Provides a mapping from {ns,name} to counts of that instance
  unordered_map<myPair<string,string>,uint> insts;
  public:
    InstanceDAG() {}
    void insert(string ns, string name) {
      insts[{ns,name}] +=1;
      cout << "D Insert: " << ns << "." << name << " " << insts.count({ns,name}) << endl;
    }
    void remove(string ns, string name) {
      if (insts.count({ns,name}) <=1) {
        insts.erase({ns,name});
      }
      else {
        insts[{ns,name}] -=1 ;
      }
      cout << "D Remove: " << ns << "." << name << " " << insts.count({ns,name}) << endl;
    }
    vector<myPair<string,string>> get() {
      vector<myPair<string,string>> keys;
      for (auto k : insts) keys.push_back(k.first);
      return keys;
    }
};


