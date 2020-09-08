#ifndef COREIR_WIREABLE_HPP_
#define COREIR_WIREABLE_HPP_

#include "fwd_declare.h"
#include "metadata.h"

namespace CoreIR {

class InstanceGraphNode;

class Wireable : public MetaData {
 public:
  enum WireableKind { WK_Interface, WK_Instance, WK_Select, WK_InstanceSelect };

 protected:
  WireableKind kind;
  ModuleDef* container;  // ModuleDef which it is contained in
  Type* type;
  Wireable* topParent = nullptr;

  std::set<Wireable*> connected;

  // This manages the memory for the selects
  std::map<std::string, Select*> selects;
  SelectPath selectpath;

 public:
  Wireable(WireableKind kind, ModuleDef* container, Type* type)
      : MetaData(),
        kind(kind),
        container(container),
        type(type) {}
  virtual ~Wireable();
  virtual std::string toString() const = 0;
  const std::set<Wireable*>& getConnectedWireables() { return connected; }
  const std::map<std::string, Select*>& getSelects() { return selects; }
  ModuleDef* getContainer() { return container; }
  Context* getContext();
  WireableKind getKind() const { return kind; }
  Type* getType() { return type; }
  void addConnectedWireable(Wireable* w) { connected.insert(w); }
  void removeConnectedWireable(Wireable* w) {
    assert(connected.count(w) > 0);
    connected.erase(w);
  }

  Select* sel(const std::string&);
  Select* sel(uint);
  Select* sel(const SelectPath&);

  // Ignore These
  Select* sel(std::initializer_list<const char*> path);
  Select* sel(std::initializer_list<std::string> path);

  bool canSel(std::string);
  bool canSel(SelectPath);

  // Connect this to w
  void connect(Wireable* w);

  // Disconnect everything from this wireable
  // NOTE This invalidates iterators from getConnectedWireables() and
  // getConnections(). Do not call while iterating over these
  void disconnect();
  void disconnectAll();

  // if this wireable is from add3inst.a.b[0], then this will look like
  // {add3inst,a,b,0}
  SelectPath& getSelectPath();
  ConstSelectPath getConstSelectPath();
  std::string wireableKind2Str(WireableKind wb);

  // TODO turn these into iterators instead

  // Will return all of the selects (include self)
  // Used for traversing type hierarchy downwards
  std::map<SelectPath, Wireable*> getAllSelects();
  std::map<SelectPath, Wireable*> getAllParents();

  // Get all the connections from self and all the selects
  LocalConnections getLocalConnections();

  // NOTE: Will cache the result, assumes that the parent never change
  Wireable* getTopParent();

  // removes the select from this wireble.
  // Note this invalides iterators from getSelects()
  void removeSel(std::string selStr);

 protected:
  // This should be used very carefully. Could make things inconsistent
  friend class InstanceGraphNode;
  void setType(Type* t) { type = t; }
};

std::ostream& operator<<(std::ostream&, const Wireable&);

class Interface : public Wireable {
  const std::string instname = "self";

 public:
  Interface(ModuleDef* container, Type* type)
      : Wireable(WK_Interface, container, type){};
  static bool classof(const Wireable* w) {
    return w->getKind() == WK_Interface;
  }
  std::string toString() const;
  const std::string& getInstname() { return instname; }
};

class Instance : public Wireable {
  const std::string instname;
  Module* moduleRef;
  Values modargs;

 public:
  Instance(
    ModuleDef* container,
    std::string instname,
    Module* moduleRef,
    Values modargs);
  static bool classof(const Wireable* w) { return w->getKind() == WK_Instance; }
  std::string toString() const;
  json toJson();
  const std::string& getInstname() const { return instname; }
  const Values& getModArgs() const { return modargs; }
  bool hasModArgs() { return !modargs.empty(); }

  Module* getModuleRef() { return moduleRef; }

  void replace(Module* moduleRef, Values modargs = Values());
  // void replace(Generator* generatorRef, Values genargs, Values
  // modargs=Values());

  bool canSel(std::string);
  bool canSel(SelectPath);

  using Wireable::sel;  // for overloaded sel
  Select* sel(const std::string&);

  friend class InstanceGraphNode;
};

class Select : public Wireable {
 protected:
  Wireable* parent;
  std::string selStr;

 public:
  Select(ModuleDef* container, Wireable* parent, std::string selStr, Type* type)
      : Select(WK_Select, container, parent, selStr, type) {}
  // Accept kind as first argument so child class can override
  Select(
    WireableKind wireable_kind,
    ModuleDef* container,
    Wireable* parent,
    std::string selStr,
    Type* type)
      : Wireable(wireable_kind, container, type),
        parent(parent),
        selStr(selStr) {}
  static bool classof(const Wireable* w) { return w->getKind() == WK_Select; }
  std::string toString() const;
  Wireable* getParent() { return parent; }
  const std::string& getSelStr() { return selStr; }
};

class InstanceSelect : public Select {
 private:
  Wireable* wrapped_wireable;

 public:
  InstanceSelect(
    ModuleDef* container,
    Wireable* parent,
    std::string selStr,
    Wireable* wrapped_wireable)
      : Select(
          WK_InstanceSelect,
          container,
          parent,
          selStr,
          wrapped_wireable->getType()),
        wrapped_wireable(wrapped_wireable) {}
  static bool classof(const Wireable* w) {
    return w->getKind() == WK_InstanceSelect;
  }

  bool canSel(std::string);
  bool canSel(SelectPath);

  using Wireable::sel;  // for overloaded sel
  Select* sel(const std::string&);
};

}  // namespace CoreIR

#endif  // WIREABLE_HPP_
