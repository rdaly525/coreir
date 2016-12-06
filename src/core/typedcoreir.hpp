class _TypedWireable {
  protected :
    WireableEnum bundleType;
    Module* container; // Module which it is contained in 
    Type* type;
    //TODO should I save head during construction? or figure it out at access
    //WireableEnum* head; //Either an interface or an instance (or Constant?)
    
    bool _parentWired; // a parent is either _wired or _parentWired
    bool _wired; //I am wired (entirely). Implies connections contains at least one
    bool _childrenWired; //some children *inputs* are wired

    vector<Wireable*> connections; 
    map<string,Wireable*> children;
  public :
    Wireable(WireableEnum bundleType, Module* container, Type* type) : bundleType(bundleType),  container(container), type(type), _parentWired(false), _wired(false), _childrenWired(false) {}
    virtual ~Wireable() {}
    virtual string _string(void)=0;
    bool isType(WireableEnum b) {return bundleType==b;}
    WireableEnum getBundleType() { return bundleType; }
    void addChild(string sel,Wireable* wb);
    bool isParentWired() { return _parentWired;}
    bool isWired() {return _wired;}
    bool hasChildrenWired() {return _childrenWired;}
    void setParentWired(); //Set _parentWired and all children's setParentWired
    void addConnection(Wireable* w); //Set _wired and all children's setParentWired
    virtual void setChildrenWired() {_childrenWired = true;}
    bool checkWired(); //recursively checks if wired
    Select* sel(string);
    Select* sel(uint);
    Module* getContainer(void) { return container;}
    Type* getType(void) { return type;}

};

class _TypedInterface : public _TypedWireable {
  public :
    Interface(Module* container, Type* type) : Wireable(IFACE,container,type) {}
    ~Interface() {}
    string _string();
};

class _TypedInstance : public _TypedWireable {
  string name;
  Circuit* circuitType;
  public :
    Instance(Module* container, Type* type, string name, Circuit* circuitType) : Wireable(INST,container,type), name(name), circuitType(circuitType) {}
    ~Instance() {}
    string _string();
    Circuit* getCircuitType() {return circuitType;}
    string getName() { return name; }
    void replace(Circuit* c) {circuitType = c;} //TODO dangerous. Could point to its container.
};

class _TypedSelect : public _TypedWireable {
  Wireable* parent;
  string selStr;
  public :
    Select(Module* container, Type* type, Wireable* parent, string selStr);
    ~Select() {}
    string _string();
    void setChildrenWired() {_childrenWired=true; parent->setChildrenWired();}
    Wireable* getParent() { return parent; }
    string getSelStr() { return selStr; }
};

