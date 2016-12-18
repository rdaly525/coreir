#ifndef TYPEDCOREIR_HPP_
#define TYPEDCOREIR_HPP_

#include "coreir.hpp"

class TypedModuleDef : public ModuleDef {
 
  public :
    TypedModuleDef(string name, Type* type);
    virtual ~TypedModuleDef() {}

    // This interface must look the same
    Instance* addInstance(string,Instantiable*, GenArgs* = nullptr);
    void wire(Wireable* a, Wireable* b);
};

class TypedWire : public Wire {
  protected :
    Type* type;
    

  public :
    bool _parentWired; // a parent is either _wired or _parentWired
    bool _wired; //I am wired (entirely). Implies connections contains at least one
    bool _childrenWired; //some children *inputs* are wired
 
    
    
    TypedWire(Type* type,Wireable* from, Wire* parent=nullptr) : Wire(from,parent), type(type), _parentWired(false), _wired(false), _childrenWired(false) {}
    virtual ~TypedWire() {}
    string toString() const { return "TypedWire of type: " + type->toString();}
    
    // new stuff
    Type* getType(void) { return type;}
    bool isWired() {return _wired;}
    bool isParentWired() { return _parentWired;}
    void setParentWired(); //Set _parentWired and all children's setParentWired
    bool hasChildrenWired() {return _childrenWired;}
    void setChildrenWired();
    
    void addWiring(Wire* w); //Set _wired and all children's setParentWired
    void checkWired(); //recursively checks if wired
};

class TypedInterface : public Interface {
  public :
    TypedInterface(ModuleDef* container, Type* type) : Interface(container,TIFACE) {
      delete wire;
      wire = new TypedWire(type,this);
    }
    ~TypedInterface() {}
    Select* sel(string);
    //string toString() const {return Interface::toString();}
};

class TypedInstance : public Instance {
  public :
    TypedInstance(ModuleDef* container, Type* type, string instname, TypedModuleDef* tmodRef) : Instance(container, instname,tmodRef,nullptr,TINST) {
      delete wire;
      wire = new TypedWire(type,this);
    }
    ~TypedInstance() {}
    Select* sel(string);
    string toString() const {return Instance::toString();}
};

class TypedSelect : public Select {
  public :
    TypedSelect(TypedModuleDef* container, Type* type, Wireable* parent, string selStr) : Select(container,parent,selStr,TSEL) {
      TypedWire* twire = new TypedWire(type,this);
      TypedWire* twparent = castTypedWire(parent->wire);
      
      twire->_parentWired = twparent->isWired() || twparent->isParentWired();
      wire = twire;
      parent->wire->addChild(selStr,wire);

    }  
    ~TypedSelect() {}
    Select* sel(string);
    void setChildrenWired();
    string toString() const {return Select::toString();}
};

#endif //TYPEDCOREIR_HPP_
