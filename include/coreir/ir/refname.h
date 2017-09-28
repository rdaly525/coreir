#ifndef COREIR_REFNAME_HPP_
#define COREIR_REFNAME_HPP_

namespace CoreIR {
//Class is used as a generic class for holding namespace+name combo
class RefName {
  protected :
    Namespace* ns;
    std::string name;
    RefName(Namespace* ns, std::string name) : ns(ns), name(name) {}
  public :
    Namespace* getNamespace() { return ns;}
    Context* getContext();
    const std::string& getName() const { return name;}
    std::string getRefName() const;

}

}
#endif
