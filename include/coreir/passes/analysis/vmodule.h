/* vim: set tabstop=2:softtabstop=2:shiftwidth=2 */

#ifndef COREIR_VMODULE_HPP_
#define COREIR_VMODULE_HPP_

#include <queue>
#include <regex>
#include "coreir.h"

// TODO get rid of
using namespace std;

namespace CoreIR {
namespace Passes {
namespace VerilogNamespace {

namespace {
std::string toConstString(Value* v) {
  if (auto av = dyn_cast<Arg>(v)) { return av->getField(); }
  else if (auto iv = dyn_cast<ConstInt>(v)) {
    return iv->toString();
  }
  else if (auto bv = dyn_cast<ConstBool>(v)) {
    return std::to_string(uint(bv->get()));
  }
  else if (auto bvv = dyn_cast<ConstBitVector>(v)) {
    BitVector bv = bvv->get();
    // return
    // std::to_string(bv.bitLength())+"'d"+std::to_string(bv.to_type<uint64_t>());

    // return std::to_string(bv.bitLength()) + "'b" + bv.binary_string();
    return bv.hex_string();
  }
  else if (auto sv = dyn_cast<ConstString>(v)) {
    return std::string("\"") + sv->toString() + std::string("\"");
  }
  coreir_unreachable();
}
}  // namespace

struct VModule;
struct VModules {
  vector<VModule*> mods;
  map<Module*, VModule*> mod2VMod;
  vector<VModule*> vmods;
  bool _inline = false;
  bool _verilator_debug = false;
  // Only used for genetaors that have verilog
  map<Generator*, VModule*> gen2VMod;

  vector<VModule*> externalVMods;

  void addModule(Module* m);
};

struct VWire {
  std::string name;
  bool isArray;
  unsigned dim;
  Type::DirKind dir;

  VWire(std::string field, Type* t)
      : name(field),
        isArray(isa<ArrayType>(t)),
        dim(t->getSize()),
        dir(t->getDir()) {}
  VWire(Wireable* w) : VWire("", w->getType()) {
    SelectPath sp = w->getSelectPath();
    if (sp.size() == 3) {
      ASSERT(dim == 1 && !isNumber(sp[1]) && isNumber(sp[2]), "DEBUG ME:");
      name = sp[1] + "[" + sp[2] + "]";
    }
    else if (sp.size() == 2) {
      ASSERT(!isNumber(sp[1]), "DEBUG ME:");
      name = sp[1];
    }
    else {
      assert(0);
    }
    if (sp[0] != "self") { name = sp[0] + "__" + name; }
  }
  VWire(std::string name, unsigned dim, Type::DirKind dir)
      : name(name),
        dim(dim),
        dir(dir) {}
  std::string dimstr() {
    if (!isArray) return "";
    return "[" + std::to_string(dim - 1) + ":0]";
  }
  std::string dirstr() {
    if (dir == Type::DK_In) { return "input"; }
    else if (dir == Type::DK_Out) {
      return "output";
    }
    else if (dir == Type::DK_InOut) {
      return "inout";
    }
    else {
      ASSERT(false, "dirstr not implemented for dir=" + toString(dir));
    }
  }
  std::string getName() { return name; }
};

struct VModule {
  bool inlineable = false;
  typedef std::set<std::string> SParams;
  typedef std::map<std::string, std::string> SMap;
  std::string modname = "";
  std::map<std::string, VWire> ports;
  std::vector<std::string> interface;
  SParams params;
  SMap paramDefaults;
  std::vector<std::string> stmts;
  VModules* vmods;
  string modComment = "";
  string verilog_string = "";

  bool isExternal = false;
  VModule(VModules* vmods) : vmods(vmods) {}
  virtual ~VModule() {}
  void addStmt(std::string stmt) { stmts.push_back(stmt); }
  void addComment(std::string stmt, string tab = "  ") {
    stmts.push_back(tab + "// " + stmt);
  }

  std::string toString() const;

  std::string toInstanceString(Instance* inst);

  void Type2Ports(Type* t, std::map<std::string, VWire>& ports) {

    for (auto rmap : cast<RecordType>(t)->getRecord()) {
      ports.emplace(rmap.first, VWire(rmap.first, rmap.second));
    }
  }

  std::string p2Str(std::set<std::string> ss) {
    return "(" + join(ss.begin(), ss.end(), string(",")) + ")";
  }
  void addParams(Params ps) {
    for (auto p : ps) {
      ASSERT(
        this->params.count(p.first) == 0,
        "NYI Cannot have duplicate params\n" + this->p2Str(params) +
          " already has " + p.first);
      this->params.insert(p.first);
    }
  }
  void addDefaults(Values ds) {
    for (auto dpair : ds) {
      ASSERT(
        this->params.count(dpair.first),
        modname + " NYI Cannot Add default! " + dpair.first);
      this->paramDefaults[dpair.first] = toConstString(dpair.second);
    }
  }
};

struct VObject;

class VObjComp {
 public:
  bool operator()(const VObject* l, const VObject* r) const;
};

struct CoreIRVModule : VModule {
  Module* mod;
  // Backwards maps
  std::map<Instance*, VObject*> inst2VObj;
  std::map<string, std::set<VObject*, VObjComp>> sortedVObj;

  void addConnectionsInlined(ModuleDef* def);
  void addConnections(ModuleDef* def);
  void addInstance(Instance* inst);
  std::string inline_instance(
    ModuleDef* def,
    std::queue<Connection>& worklist,
    Instance* right_parent);
  std::string get_replace_str(
    std::string input_name,
    Instance* instance,
    ModuleDef* def,
    std::queue<Connection>& worklist);
  std::string get_inline_str(
    Wireable* sink,
    SelectPath select_path,
    Connection conn,
    ModuleDef* def,
    std::queue<Connection>& worklist);

  CoreIRVModule(VModules* vmods, Module* m);
};

// The following are for CoreIR VModules
// This represents some chunk of lines of code
struct VObject {
  string name;
  int priority = 0;  // Lower is earilier in the file
  string file = "_";
  int line = -1;
  VObject(string name) : name(name) {}
  VObject(string name, string file, int line)
      : name(name),
        file(file),
        line(line) {}
  // fills out the body
  virtual void materialize(CoreIRVModule* vmod) = 0;
};

struct VInstance : VObject {
  string wireDecs;
  VModules* vmods;
  Instance* inst;
  VInstance(VModules* vmods, Instance* inst)
      : VObject(toString(inst)),
        vmods(vmods),
        inst(inst) {
    assert(inst);
    this->line = -100000;
    this->priority = 0;
    auto meta = inst->getMetaData();
    if (meta.count("filename")) { this->file = meta["filename"].get<string>(); }
    if (meta.count("lineno")) {
      this->line = std::stoi(meta["lineno"].get<string>());
    }

    Module* mref = inst->getModuleRef();
    vector<string> wires;
    for (auto rmap : cast<RecordType>(mref->getType())->getRecord()) {
      wires.push_back(
        VWireDec(VWire(inst->getInstname() + "__" + rmap.first, rmap.second)));
    }
    wireDecs = join(wires.begin(), wires.end(), string("\n"));
  }

  string VWireDec(VWire w) {
    string s = "  wire " + w.dimstr() + " " + w.getName();
    if (this->vmods->_verilator_debug) { s += "/*verilator public*/"; }
    return s + ";";
  }

  virtual void materialize(CoreIRVModule* vmod) override {
    Module* mref = inst->getModuleRef();
    VModule* vref = vmods->mod2VMod[mref];
    assert(vref);
    if (this->line > 0) {
      vmod->addComment("Instanced at line " + to_string(this->line));
    }
    if (mref->isGenerated()) {
      vmod->addComment(
        "Instancing generated Module: " + mref->getRefName() +
        toString(mref->getGenArgs()));
    }
    vmod->addStmt(wireDecs);
    vmod->addStmt(vref->toInstanceString(inst));
  }
};

struct VAssign : VObject {
  Connection conn;
  ModuleDef* def;
  VAssign(ModuleDef* def, Connection conn)
      : VObject(toString(conn)),
        conn(conn) {
    this->line = -1;  // largest number to go at the top of the bottom
    this->priority = 1;
    if (def->hasMetaData(conn.first, conn.second)) {
      auto meta = def->getMetaData(conn.first, conn.second);
      if (meta.count("filename")) {
        this->file = meta["filename"].get<string>();
      }
      if (meta.count("lineno")) {
        this->line = std::stoi(meta["lineno"].get<string>());
      }
    }
  }
  void materialize(CoreIRVModule* vmod) override {
    Wireable* left = conn.first->getType()->getDir() == Type::DK_In
      ? conn.first
      : conn.second;
    Wireable* right = left == conn.first ? conn.second : conn.first;
    VWire vleft(left);
    VWire vright(right);
    if (this->line > 0) {
      vmod->addComment("Wired at line: " + to_string(this->line));
    }
    vmod->addStmt(
      "  assign " + vleft.getName() + vleft.dimstr() + " = " +
      vright.getName() + vright.dimstr() + ";");
  }
};

// Assign a wireable to a string
struct VAssignStr : VObject {
  Wireable* target;
  ModuleDef* def;
  std::string value_str;
  VAssignStr(ModuleDef* def, Wireable* target, std::string value_str)
      : VObject(toString(target) + value_str),
        target(target),
        value_str(value_str) {
    this->line = -1;  // largest number to go at the top of the bottom
    this->priority = 1;
    // Ignore metadata for inlining until we have a good proposal for how to
    // handle this
  }
  void materialize(CoreIRVModule* vmod) override {
    VWire vtarget(target);
    // Ignore metadata for inlining until we have a good proposal for how to
    // handle this
    vmod->addStmt(
      "  assign " + vtarget.getName() + vtarget.dimstr() + " = " + value_str +
      ";");
  }
};

struct ExternVModule : VModule {

  ExternVModule(VModules* vmods, Module* m) : VModule(vmods) {
    Type2Ports(m->getType(), this->ports);
    this->modname = m->getName();
    this->isExternal = true;
  }
};

// Verilog VModules
struct VerilogVModule : VModule {
  json jver;
  VerilogVModule(VModules* vmods, Module* m) : VModule(vmods) {
    Type2Ports(m->getType(), this->ports);
    this->addParams(m->getModParams());
    this->addDefaults(m->getDefaultModArgs());
    this->addJson(m->getMetaData(), m->getName());
  }
  VerilogVModule(VModules* vmods) : VModule(vmods) {}
  void addJson(json& jmeta, string name) {
    assert(jmeta.count("verilog") > 0);
    ASSERT(name != "", name);
    this->modname = name;
    jver = jmeta["verilog"];
    if (jver.count("verilog_string")) {
      this->modname = name;
      this->verilog_string = jver["verilog_string"].get<std::string>();
      // Ensure that if the field verilog_string is included that the remaining
      // fields are not included.
#define VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, field)                          \
  ASSERT(                                                                      \
    jver.count(field) == 0,                                                    \
    string("Can not include ") + string(field) +                               \
      string(" with verilog_string"))
      VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, "prefix");
      VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, "definition");
      VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, "interface");
      VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, "parameters");
      VERILOG_FULL_MODULE_ASSERT_MUTEX(jver, "inlineable");
#undef VERILOG_FULL_MODULE_ASSERT_MUTEX
      // TODO(rsetaluri): Issue warning that we are including black-box
      // verilog. Most importantly the user should know that there is *no
      // guarantee* at this level that things are in sync. For example, if the
      // CoreIR module declaration does not match the verilog's, then the output
      // may be garbage for downstream tools.
      return;
    }
    if (jver.count("prefix")) {
      this->modname = jver["prefix"].get<std::string>() + name;
    }
    if (jver.count("definition")) {
      if (
        this->vmods->_verilator_debug &&
        jver.count("verilator_debug_definition") > 0) {
        stmts.push_back(jver["verilator_debug_definition"].get<std::string>());
      }
      else {
        stmts.push_back(jver["definition"].get<std::string>());
      }
    }
    if (jver.count("interface")) {
      interface = (jver["interface"].get<std::vector<std::string>>());
    }
    if (jver.count("parameters")) {
      for (auto p : jver["parameters"].get<std::vector<std::string>>()) {
        this->params.insert(p);
      }
    }
    if (jver.count("inlineable") && jver["inlineable"].get<bool>()) {
      this->inlineable = true;
    }
  }
};

// Need to add
struct ParamVerilogVModule : VerilogVModule {
  ParamVerilogVModule(VModules* vmods, Generator* g) : VerilogVModule(vmods) {
    this->addParams(g->getGenParams());
    this->addDefaults(g->getDefaultGenArgs());
    this->addJson(g->getMetaData(), g->getName());
  }
};

}  // namespace VerilogNamespace
}  // namespace Passes
}  // namespace CoreIR

#endif
