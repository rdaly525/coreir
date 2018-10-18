#ifndef COREIR_REFNAME_HPP_
#define COREIR_REFNAME_HPP_

#include "fwd_declare.h"
#include "metadata.h"

namespace CoreIR {

  
class GlobalValue: public MetaData {
  public :
    enum GlobalValueKind {GVK_Module,GVK_Generator,GVK_TypeGen,GVK_NamedType};
    //enum LinkageKind {LK_Namespace=0, LK_Generated=1}; TODO
  protected:
    GlobalValueKind kind;
    Namespace* ns;
    std::string name;
    GlobalValue(GlobalValueKind kind, Namespace* ns, std::string name);
    
  public :
    GlobalValueKind getKind() const { return kind;}
    Namespace* getNamespace() { return ns;}
    Context* getContext();
    const std::string& getName() const { return name;}
    std::string getRefName() const;
 
    virtual std::string toString() const =0;
    virtual void print() const = 0;
    friend bool operator==(const GlobalValue& l,const GlobalValue& r);
    
};

std::ostream& operator<<(std::ostream& os, const GlobalValue&);
  
}
#endif
