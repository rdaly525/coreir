#include "coreir.h"
#include "coreir/passes/analysis/magma.h"

using namespace std;
using namespace CoreIR;

string type2magma(Context* c,Type* t) {
  //if (auto rt = dyn_cast<RecordType>(t)) {
  //  ASSERT(0,"NYI");   
  //  //vector<string> sels;
  //  //if (!rt->isMixed()) {
  //  //  for (auto rec : rt->getRecord()) {
  //  //    sels.push_back(rec.first + " : " + type2magma(rec.second,isInput));
  //  //  }
  //  //}
  //  //else {
  //  //  ASSERT(0,"NYI Bundles");
  //  //}
  //  //return join(sels.begin(),sels.end(),string(", "));
  //}
  if (auto at = dyn_cast<ArrayType>(t)) {
    Type* et = at->getElemType();
    return "Array("+to_string(at->getLen())+"," + type2magma(c,et) + ")";
  }
  else if (auto nt = dyn_cast<NamedType>(t)) {
    if (nt == c->Named("coreir.clkIn")) return "In(Clock)";
    else if (nt == c->Named("coreir.clk")) return "Out(Clock)";
    else ASSERT(0,"NYI: " + nt->toString());
  }
  else if (isa<BitInType>(t)) {
    return "In(Bit)";
  }
  else if (isa<BitType>(t)) {
    return "Out(Bit)";
  }
  else {
    ASSERT(0,"DEBUGME: " +t->toString());
  }
}

namespace {
std::string ReplaceString(std::string subject, const std::string& search, const std::string& replace) {
  size_t pos = 0;
  while ((pos = subject.find(search, pos)) != std::string::npos) {
    subject.replace(pos, search.length(), replace);
    pos += replace.length();
  }
  return subject;
}
}

void CoreIR::Passes::MModule::addIO(RecordType* rt) {
  for (auto rpair : rt->getRecord()) {
    io.push_back("\""+rpair.first+"\"");
    io.push_back(type2magma(c,rpair.second));
  }
}
namespace {
string sp2Str(SelectPath sp) {
  string ret = sp[0];
  sp.pop_front();
  for (auto s : sp) {
    if (isNumber(s)) ret  = ret +"[" + s + "]";
    else ret = "getattr("+ret+", \"" + s+"\")";
  }
  return ret;
}
}
string toWire(SelectPath snk, SelectPath src) {
  if (src[0] == "self") src[0] = "io";
  if (snk[0] == "self") snk[0] = "io";
  string ret = "wire("+sp2Str(snk) + ", " + sp2Str(src)+")";
  return ReplaceString(ret,string("$"),string("__ds__"));
}

string toUpper(string s) {
  int f = s[0];
  assert( f-'a' >=0 && 'z'-f >=0);
  s[0] = s[0]-'a'+'A';
  return s;
}

std::string CoreIR::Passes::MModule::toName(Module* m) {
  if (m->getNamespace()->getName() == "coreir") {
    return "mantle.coreir.DefineCoreir" + toUpper(m->getName());
  }
  else if (m->getNamespace()->getName() == "corebit") {
    return "mantle.coreir.DefineCorebit" + toUpper(m->getName());
  }
  return m->getNamespace()->getName() + "_" + m->getLongName();
}

string BV2Str(Value* v) {
  BitVector bv = cast<ConstBitVector>(v)->get();
  return "(" + to_string(bv.to_type<uint>()) + ", " + to_string(bv.bitLength()) + ")";
}

string V2MStr(Value* v) {
  if (auto vbv = dyn_cast<ConstBitVector>(v)) {
    return to_string(vbv->get().to_type<uint>());
  }
  else if (auto vint = dyn_cast<ConstInt>(v)) {
    return to_string(vint->get());
  }
  else if (auto vbool = dyn_cast<ConstBool>(v)) {
    return vbool->get() ? "1" : "0";
  }
  else if (auto varg = dyn_cast<Arg>(v)) {
    return varg->getField();
  }
  ASSERT(0,"DEBUGME");
  return "";
}

string Values2MStr(Values vs) {
  vector<string> ss;
  for (auto vpair : vs) {
    ss.push_back(vpair.first+"="+V2MStr(vpair.second));
  }
  return "("+join(ss.begin(),ss.end(),string(", "))+")";
}

string CoreIR::Passes::MModule::toInstanceString(string iname, Values modargs) {
  iname = ReplaceString(iname,string("$"),string("__ds__"));
  if (m->getNamespace()->getName() == "coreir") {
    mergeValues(modargs,m->getGenArgs());
    return this->name + Values2MStr(modargs) + "(name=" + "\""+iname+"\")";
  }
  else if (m->getNamespace()->getName() == "corebit") {
    return this->name + Values2MStr(modargs) + "(name=" + "\""+iname+"\")";
  }
  else if (modargs.size()) {
    return "Define_" + this->name + Values2MStr(modargs) + "()";
  }
  else {
    return this->name + "()";
  }
}

string Params2MStr(Params ps) {
  vector<string> ss;
  for (auto p : ps) {
    ss.push_back(p.first);
  }
  return "("+join(ss.begin(),ss.end(),string(", "))+")";
}

string CoreIR::Passes::MModule::toString() {
  vector<string> lines;
  string ts = "";
  string magname = "\"" + this->name + "\"";
  string fname;
  if (m->getModParams().size()) {
    lines.push_back("@cache_definition");
    fname = "Define_" + this->name + Params2MStr(m->getModParams());
    lines.push_back("def " + fname +":");
    ts = "  ";
    magname = "f\""+this->name;
    for (auto p : m->getModParams()) {
      magname = magname + "_{"+p.first+"}";
    }
    magname = magname + "\"";
  }
  lines.push_back(ts + "class " + this->name + "(Circuit):");
  lines.push_back(ts + "  name = " + magname);
  lines.push_back(ts + "  IO = [" +join(this->io.begin(),this->io.end(),string(", "))+"]");
  lines.push_back(ts + "  @classmethod");
  lines.push_back(ts + "  def definition(io):");
  for (auto s : this->stmts) {
    lines.push_back(ts + "    " + s);
  }
  if (m->getModParams().size()) {
    lines.push_back(ts + "return " + this->name);
  }
  string ret = join(lines.begin(),lines.end(),string("\n"));
  return ret;
}


string Passes::Magma::ID = "magma";
bool Passes::Magma::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* m = node.getModule();
  ASSERT(modMap.count(m)==0,"DEBUGME");
  
  MModule* fm;
  
  fm = new MModule(m);
  this->modMap[m] = fm;
  if (m->getNamespace()->getName() != "corebit" && m->getNamespace()->getName() != "coreir") {
    this->mmods.push_back(fm);
  }
  
  if (!m->hasDef()) return false;
  ModuleDef* def = m->getDef();
  
  //First add all instances
  for (auto instpair : def->getInstances()) {
    Instance* inst = instpair.second;
    string iname = instpair.first;
    Module* mref = inst->getModuleRef();
    ASSERT(modMap.count(mref),"DEBUGMEs");
    MModule* fmref = modMap[mref];

    iname = ReplaceString(iname,string("$"),string("__ds__"));
    fm->addStmt(iname + " = " + fmref->toInstanceString(iname,inst->getModArgs()));
  }

  //Then add all connections
  auto dm = m->newDirectedModule();
  for (auto dcon : dm->getConnections()) {
    SelectPath src = dcon->getSrc();
    SelectPath snk = dcon->getSnk();
    fm->addStmt(toWire(snk,src));
  }
  return false;
}

void Passes::Magma::writeToStream(std::ostream& os) {
  Module* top = getContext()->getTop();
  ASSERT(top, "Magma requires a top module");
  ASSERT(modMap.count(top),"DEBUGME");
  os << "import os" << endl;
  os << "os.environ['MANTLE'] = 'coreir'" << endl;
  os << "from magma import *" << endl;
  os << "from mantle import *" << endl;
  os << "import mantle.coreir" << endl;
  os << endl;
  for (auto fm : mmods) {
    os << fm->toString() << endl << endl;
  }
}






