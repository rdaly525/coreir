/* vim: set tabstop=2:softtabstop=2:shiftwidth=2 */

#include "coreir/passes/analysis/vmodule.h"
#include "coreir.h"

namespace CoreIR {
namespace Passes {
namespace VerilogNamespace {

CoreIRVModule::CoreIRVModule(VModules* vmods, Module* m) : VModule(vmods) {
  Type2Ports(m->getType(), this->ports);
  assert(m->hasDef());
  this->modname = m->getLongName();
  if (m->isGenerated()) {
    this->modComment = "// Generated from " + m->getRefName() +
      ::CoreIR::toString(m->getGenArgs());
  }
  this->addParams(m->getModParams());
  this->addDefaults(m->getDefaultModArgs());
  ModuleDef* def = m->getDef();
  for (auto imap : def->getInstances()) { this->addInstance(imap.second); }
  if (vmods->_inline) { this->addConnectionsInlined(def); }
  else {
    this->addConnections(def);
  }
  // Materialize all the statemts
  for (auto fpair : sortedVObj) {
    string file = fpair.first;
    this->addStmt("");
    if (file != "_") { this->addComment("Compiled from " + file); }
    for (auto vobj : fpair.second) {
      this->addStmt("");
      vobj->materialize(this);
    }
    this->addStmt("");
  }
}

// Returns true if the select path starts with "self" and the direction of the
// type in DK_In
static bool is_input_from_self(Wireable* wireable) {
  return wireable->getSelectPath()[0] == "self" &&
    wireable->getType()->getDir() == Type::DK_In;
}

// Helper function to initialize work list with connections feeding the module
// def outputs
static void init_worklist(ModuleDef* def, std::queue<Connection>& worklist) {
  for (auto conn : def->getSortedConnections()) {
    if (is_input_from_self(conn.first) || is_input_from_self(conn.second)) {
      worklist.push(conn);
    }
  }
}

// https://stackoverflow.com/questions/216823/whats-the-best-way-to-trim-stdstring
static inline void ltrim(std::string& s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) {
            return !std::isspace(ch);
          }));
}

static bool str_in_select_path(SelectPath select_path, std::string search_str) {
  for (auto item : select_path) {
    if (item == search_str) { return true; }
  }
  return false;
}

std::string CoreIRVModule::get_inline_str(
  Wireable* source,
  SelectPath select_path,
  Connection conn,
  ModuleDef* def,
  std::queue<Connection>& worklist) {
  std::string to_replace;
  if (select_path[0] == "self") {
    // If it's a reference to an input port, just inline the reference directly
    to_replace = VWire(source).getName();
  }
  else {
    // Otherwise, we try to get the result of inlining the instance (which may
    // recursively inline other instances)
    Instance* inst = dyn_cast<Instance>(def->sel(select_path[0]));
    std::string result = inline_instance(def, worklist, inst);
    if (result == "") {
      // If the instance can't be inlined, denoted by empty string, we just
      // replace it with the standard wire name
      to_replace = VWire(source).getName();
      worklist.push(conn);
    }
    else {
      // Otherwise, use the result of inlining
      to_replace = result;
    }
  }
  return to_replace;
}

std::string CoreIRVModule::get_replace_str(
  std::string input_name,
  Instance* instance,
  ModuleDef* def,
  std::queue<Connection>& worklist) {
  std::string replace_str = "";
  // Track the number of connections added, if more than one, we use verilog
  // concat syntax
  int count = 0;

  for (auto conn : def->getSortedConnections()) {
    SelectPath sp_first = conn.first->getSelectPath();
    SelectPath sp_second = conn.second->getSelectPath();
    SelectPath inst_sp = instance->getSelectPath();
    // Assume instance is first
    Wireable* source = conn.second;
    std::string to_replace = "";
    if (sp_first[0] == inst_sp[0] && str_in_select_path(sp_first, input_name)) {
      to_replace = get_inline_str(source, sp_second, conn, def, worklist);
    }
    else if (
      sp_second[0] == inst_sp[0] && str_in_select_path(sp_second, input_name)) {
      // Swap if the instance is second
      source = conn.first;
      to_replace = get_inline_str(source, sp_first, conn, def, worklist);
    }
    else {
      // Skip if instance is not part of connection
      continue;
    }
    if (count) { replace_str += ", "; }
    count++;
    replace_str += to_replace;
  }
  if (count > 1) { replace_str = "{" + replace_str + "}"; }
  return replace_str;
}

std::string CoreIRVModule::inline_instance(
  ModuleDef* def,
  std::queue<Connection>& worklist,
  Instance* right_parent) {
  std::string right_conn_str = "";
  Module* right_parent_module = right_parent->getModuleRef();
  VModule* right_parent_verilog_module = vmods->mod2VMod[right_parent_module];
  if (
    auto vermod = dynamic_cast<VerilogVModule*>(right_parent_verilog_module)) {
    if (vmods->_inline && right_parent_verilog_module->inlineable) {
      right_conn_str = vermod->jver["definition"].get<string>();
      // assumes that if it's inlineable it only has one output named out

      // replace assign out = since that will be handled by the
      // current connection target
      right_conn_str = std::regex_replace(
        right_conn_str,
        std::regex("assign out = "),
        "");

      // semicolon inserted later, so we remove it now
      right_conn_str = std::regex_replace(right_conn_str, std::regex(";"), "");

      // remove any leading spaces
      ltrim(right_conn_str);

      // for each input to the instance
      for (auto record_pair :
           cast<RecordType>(right_parent->getType())->getRecord()) {
        if (record_pair.second->getDir() == Type::DK_In) {
          std::string replace = get_replace_str(
            record_pair.first,
            right_parent,
            def,
            worklist);
          // std::cout << replace << std::endl;
          ASSERT(replace != "", "Expected something to inline");
          // replace string followed by space, bracket, close paren, or
          // semicolon and prefixed by space or open paren
          //
          // TODO are there any more? This avoids issue where, for example, we
          // want to replace "in" which also matches "inst0" (so it would
          // replace the first two letters of the inst0)
          std::regex expr("( |\\()?" + record_pair.first + "( |;|\\[|\\))?");
          // Append the second match group (space, subscript, etc...), also
          // concat
          replace = "$1" + replace + "$2";
          right_conn_str = std::regex_replace(right_conn_str, expr, replace);
        }
      }
      // Search for modArgs
      for (auto pval : right_parent->getModArgs()) {
        std::regex expr(pval.first);
        string replace = toConstString(pval.second);
        right_conn_str = std::regex_replace(right_conn_str, expr, replace);
      }
      Module* mref = right_parent->getModuleRef();
      // Search for genArgs
      if (mref->isGenerated()) {
        for (auto pval : mref->getGenArgs()) {
          std::regex expr(pval.first);
          string replace = toConstString(pval.second);
          right_conn_str = std::regex_replace(right_conn_str, expr, replace);
        }
      }
    }
  }
  if (right_conn_str == "") {
    // not inlined, so add it's connections to the worklist
    for (auto conn : def->getSortedConnections()) {
      SelectPath sp_first = conn.first->getSelectPath();
      SelectPath sp_second = conn.second->getSelectPath();
      SelectPath inst_sp = right_parent->getSelectPath();
      Wireable* sink = conn.first;
      if (sp_first[0] == inst_sp[0]) {
        // Use default case
      }
      else if (sp_second[0] == inst_sp[0]) {
        // Swap if the instance is second
        sink = conn.second;
      }
      else {
        // Skip if instance is not part of connection
        continue;
      }
      // Skip inputs
      if (sink->getType()->getDir() == Type::DK_Out) { continue; }
      worklist.push(conn);
    }
  }
  return right_conn_str;
}

// Non-inlined version of connections
void CoreIRVModule::addConnections(ModuleDef* def) {
  for (auto conn : def->getSortedConnections()) {
    VObject* vassign = new VAssign(def, conn);
    sortedVObj[vassign->file].insert(vassign);
  }
}

// queue = output ports of current definition
// while queue is not empty
//     output = queue.pop()
//     if output is driven by instance that can be inlined
//         recursively inline any inputs to instance if possible, otherwise use
//         standard input wire inline the instance and have it drive the output
//         add any non-inlined inputs of the instance to the queue
//     else
//        emit code normally for the output and instance
//        add the inputs of the instance to the queue
void CoreIRVModule::addConnectionsInlined(ModuleDef* def) {
  std::queue<Connection> worklist;
  // Initialize work list with connections feeding the module def outputs
  init_worklist(def, worklist);

  while (!worklist.empty()) {
    Connection conn = worklist.front();
    worklist.pop();
    Wireable* left = conn.first->getType()->getDir() == Type::DK_In
      ? conn.first
      : conn.second;
    Wireable* right = left == conn.first ? conn.second : conn.first;
    string right_conn_str = "";
    // skip if module def input connected to output
    if (!(left->getSelectPath()[0] == "self" &&
          right->getSelectPath()[0] == "self")) {
      if (Instance* right_parent = dyn_cast<Instance>(right->getTopParent())) {
        right_conn_str = CoreIRVModule::inline_instance(
          def,
          worklist,
          right_parent);
      }
      else {
        ASSERT(
          right->getSelectPath()[0] == "self",
          "Expected reference to self port");
      }
    }
    if (right_conn_str == "") {
      VWire vright(right);
      right_conn_str = vright.getName() + vright.dimstr();
    }
    VObject* vassign = new VAssignStr(def, left, right_conn_str);
    sortedVObj[vassign->file].insert(vassign);
  }
}

// Need to choose if I am going to inline
void CoreIRVModule::addInstance(Instance* inst) {
  Module* mref = inst->getModuleRef();
  VModule* vmref = vmods->mod2VMod[mref];
  if (auto vermod = dynamic_cast<VerilogVModule*>(vmref)) {
    if (vmods->_inline && vermod->inlineable) {
      // skip inlined instance
      return;
    }
  }
  VObject* vinst = new VInstance(this->vmods, inst);
  inst2VObj[inst] = vinst;
  sortedVObj[vinst->file].insert(vinst);
}

bool VObjComp::operator()(const VObject* l, const VObject* r) const {
  if (l->line != r->line) { return l->line < r->line; }
  if (l->priority != r->priority) { return l->priority < r->priority; }
  return l->name < r->name;
}

// Orthog Cases:
// Generated Module
// Has coreir def
// Generator has verilog info
// Module has verilog info
void VModules::addModule(Module* m) {
  Generator* g = nullptr;
  bool isGen = m->isGenerated();
  if (isGen) { g = m->getGenerator(); }
  bool hasDef = m->hasDef();
  bool genHasVerilog = false;
  if (isGen) { genHasVerilog = g->getMetaData().count("verilog") > 0; }
  bool modHasVerilog = m->getMetaData().count("verilog") > 0;
  // Linking concerns:
  //   Two Verilog defs, should be an error.
  ASSERT(!(modHasVerilog && genHasVerilog), "Linking issue!");

  bool isExtern = !hasDef && !genHasVerilog && !modHasVerilog;

  // Case where VModule might already exist
  bool mightHaveVmodule = isGen && genHasVerilog;
  // cout << isGen << hasDef << genHasVerilog << modHasVerilog << isExtern <<
  // mightHaveVmodule << endl;

  // Already Created modules
  if (mightHaveVmodule && gen2VMod.count(g) > 0) {
    mod2VMod[m] = gen2VMod[g];
    return;
  }

  // Creating a new VModule
  VModule* vmod;
  if (isExtern) {
    vmod = new ExternVModule(this, m);
    externalVMods.push_back(vmod);
  }
  else if (genHasVerilog) {
    assert(gen2VMod.count(g) == 0);
    vmod = new ParamVerilogVModule(this, g);
    gen2VMod[g] = vmod;
  }
  else if (modHasVerilog) {
    vmod = new VerilogVModule(this, m);
  }
  else {
    // m is either gen or not
    vmod = new CoreIRVModule(this, m);
  }
  mod2VMod[m] = vmod;
  vmods.push_back(vmod);
}

string VModule::toString() const {
  // In the case that we want to blackbox the entirety of the module source, we
  // just return the verilog_string field.
  if (verilog_string != "") { return verilog_string; }

  assert(this->modname != "");
  vector<string> pdecs;
  if (interface.size() > 0) {
    pdecs = interface;
    if (!this->isExternal && this->vmods->_verilator_debug) {
      for (auto& pdec : pdecs) { pdec += "/*verilator public*/"; }
    }
  }
  else {
    for (auto pmap : ports) {
      auto port = pmap.second;
      string pdec = port.dirstr() + " " + port.dimstr() + " " + port.getName();
      if (!this->isExternal && this->vmods->_verilator_debug) {
        pdec += "/*verilator public*/";
      }
      pdecs.push_back(pdec);
    }
  }

  vector<string> paramstrs;
  for (auto p : params) {

    // TODO: Find a better way to deal with type parameters in wrap
    if (p != "type") {
      string defaultVal = paramDefaults.count(p) > 0 ? paramDefaults.at(p)
                                                     : "1";
      string s = "parameter " + p + "=" + defaultVal;
      paramstrs.push_back(s);
    }
  }
  string pstring = paramstrs.size() > 0
    ? " #(" + join(paramstrs.begin(), paramstrs.end(), string(", ")) + ") "
    : " ";

  ostringstream o;
  string tab = "  ";
  // Module declaration

  if (this->modComment != "") { o << this->modComment << endl; }
  o << "module " << modname << pstring << "(\n"
    << tab << join(pdecs.begin(), pdecs.end(), string(",\n  ")) << "\n);"
    << endl;

  for (auto s : stmts) o << s << endl;
  o << endl << "endmodule  // " << modname << endl;
  return o.str();
}

string VModule::toInstanceString(Instance* inst) {
  assert(this->modname != "");
  string instname = inst->getInstname();
  Module* mref = inst->getModuleRef();
  SParams params_bk = this->params;
  for (auto p : mref->getModParams()) { this->params.insert(p.first); }

  ostringstream o;
  string tab = "  ";
  string mname;
  map<string, VWire> iports;
  Values args;
  bool isVerilogGen = mref->isGenerated() &&
    mref->getGenerator()->getMetaData().count("verilog") > 0;
  if (isVerilogGen) {
    args = mref->getGenArgs();
    Type2Ports(mref->getGenerator()->getTypeGen()->getType(args), iports);
    mname = modname;
  }
  else {
    mname = modname;
    iports = ports;
  }

  for (auto amap : inst->getModArgs()) {
    ASSERT(args.count(amap.first) == 0, "NYI Alisaaed modargs/genargs");
    args[amap.first] = amap.second;
  }
  o << tab << mname << " ";

  vector<string> paramstrs;
  for (auto param : this->params) {
    ASSERT(
      args.count(param),
      "Missing parameter " + param + " from " + ::CoreIR::toString(args));

    // TODO: Remove this when we have a better solution for verilog output
    if (param != "type") {
      string astr = "." + param + "(" + toConstString(args[param]) + ")";
      paramstrs.push_back(astr);
    }
  }
  if (paramstrs.size()) {
    o << "#(" << join(paramstrs.begin(), paramstrs.end(), string(",")) << ") ";
  }
  // Assume names are <instname>_port
  vector<string> portstrs;
  for (auto port : iports) {
    string pstr = "." + port.first + "(" + instname + "__" + port.first + ")";
    portstrs.push_back(pstr);
  }
  o << instname << "(\n"
    << tab << tab << join(portstrs.begin(), portstrs.end(), ",\n" + tab + tab)
    << "\n  );";

  // TODO a bit of a hack. return params to original
  this->params = params_bk;

  return o.str();
}

}  // namespace VerilogNamespace
}  // namespace Passes
}  // namespace CoreIR
