#include <map>
#include <set>
#include "coreir/passes/analysis/coreir_json_lib.h"

using namespace CoreIR;
using namespace CoreIR::JsonLib;
using namespace std;

namespace {

string ValueType2Json(ValueType* vt) {
  if (auto bvt = dyn_cast<BitVectorType>(vt)) {
    Array a;
    a.add(quote("BitVector"));
    a.add(to_string(bvt->getWidth()));
    return a.toString();
  }
  return quote(vt->toString());
}

// Ordere these in order as well
string Params2Json(Params gp) {
  Dict j;
  for (auto it : gp) j.add(it.first, ValueType2Json(it.second));
  return j.toString();
}

string Type2Json(Type* t);
string Values2Json(Values vs);
string Value2Json(Value* v) {
  Array ret;
  ret.add(ValueType2Json(v->getValueType()));
  if (auto a = dyn_cast<Arg>(v)) {
    ret.add(quote("Arg"));
    ret.add(quote(a->getField()));
  }
  else if (auto con = dyn_cast<Const>(v)) {
    if (auto cb = dyn_cast<ConstBool>(con)) {
      ret.add(cb->get() ? "true" : "false");
    }
    else if (auto ci = dyn_cast<ConstInt>(con)) {
      ret.add(to_string(ci->get()));
    }
    else if (auto cbv = dyn_cast<ConstBitVector>(con)) {
      BitVector bv = cbv->get();
      ret.add(quote(bv.hex_string()));
    }
    else if (auto cs = dyn_cast<ConstString>(con)) {
      ret.add(quote(cs->get()));
    }
    else if (auto ct = dyn_cast<ConstCoreIRType>(con)) {
      ret.add(Type2Json(ct->get()));
    }
    else if (auto at = dyn_cast<ConstModule>(con)) {
      Module* m = at->get();
      if (m->isGenerated()) {
        Values args = m->getGenArgs();
        Array modarray;
        modarray.add(quote(m->getRefName()));
        modarray.add(Values2Json(args));
        ret.add(modarray.toString());
      }
      else {
        ret.add(quote(m->getRefName()));
      }
    }
    else if (auto cj = dyn_cast<ConstJson>(con)) {
      ret.add(CoreIR::toString(cj->get()));
    }
    else {
      ASSERT(0, "NYI");
    }
  }
  else {
    ASSERT(0, "NYI");
  }
  return ret.toString();
}

string Values2Json(Values vs) {
  Dict j;
  for (auto it : vs) j.add(it.first, Value2Json(it.second));
  return j.toString();
}

string TopType2Json(Type* t, int taboffset) {
  ASSERT(isa<RecordType>(t), "Expecting Record type but got " + t->toString());
  Array a;
  a.add(quote("Record"));
  auto rt = cast<RecordType>(t);
  Array r(taboffset);
  for (auto field : rt->getFields()) {
    Array f;
    f.add(quote(field));
    f.add(Type2Json(rt->getRecord().at(field)));
    r.add(f.toString());
  }
  a.add(r.toMultiString());
  return a.toString();
}

// One Line
string Type2Json(Type* t) {
  if (isa<BitType>(t)) return quote("Bit");
  if (isa<BitInType>(t)) return quote("BitIn");

  if (isa<BitInOutType>(t)) { return quote("BitInOut"); }
  Array a;
  if (auto nt = dyn_cast<NamedType>(t)) {
    a.add(quote("Named"));
    a.add(quote(nt->getNamespace()->getName() + "." + nt->getName()));
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    a.add(quote("Array"));
    a.add(to_string(at->getLen()));
    a.add(Type2Json(at->getElemType()));
  }
  else if (auto rt = dyn_cast<RecordType>(t)) {
    a.add(quote("Record"));
    Array r;
    for (auto field : rt->getFields()) {
      Array f;
      f.add(quote(field));
      f.add(Type2Json(rt->getRecord().at(field)));
      r.add(f.toString());
    }
    a.add(r.toString());
  }
  else {
    assert(0);
  }
  return a.toString();
}

string Instances2Json(map<string, Instance*>& insts, int taboffset) {
  Dict jis(taboffset);
  for (auto imap : insts) {
    string iname = imap.first;
    Instance* i = imap.second;
    Dict j(taboffset + 2);
    Module* m = i->getModuleRef();
    if (m->isGenerated()) {
      j.add("genref", quote(m->getGenerator()->getRefName()));
      j.add("genargs", Values2Json(m->getGenArgs()));
    }
    else {
      j.add(
        "modref",
        quote(
          i->getModuleRef()->getNamespace()->getName() + "." +
          i->getModuleRef()->getName()));
    }
    if (i->hasModArgs()) { j.add("modargs", Values2Json(i->getModArgs())); }
    if (i->hasMetaData()) { j.add("metadata", toString(i->getMetaData())); }
    jis.add(iname, j.toMultiString());
  }
  return jis.toMultiString();
}

string build_select_str(SelectPath select_path) {
  string select_str = "";
  for (auto select : select_path) {
    // Don't insert "." when there is the hierarchical select separator
    // already present
    if (select_str != "" && select[0] != ';') { select_str += "."; }
    select_str += select;
  }
  return select_str;
}

string Connections2Json(ModuleDef* def, int taboffset) {
  Array a(taboffset);

  for (auto con : def->getSortedConnections()) {
    auto pa = con.first->getSelectPath();
    auto pb = con.second->getSelectPath();
    string sa = build_select_str(pa);
    string sb = build_select_str(pb);
    Array b;
    if (sa > sb) {
      b.add(quote(sa));
      b.add(quote(sb));
    }
    else {
      b.add(quote(sb));
      b.add(quote(sa));
    }
    if (def->hasMetaData(con.first, con.second)) {
      b.add(toString(def->getMetaData(con.first, con.second)));
    }
    a.add(b.toString());
  }
  return a.toMultiString();
}

string Module2Json(Module* m, bool onlyDecl=false) {
  uint taboffset = m->isGenerated() ? 12 : 6;
  Dict j(taboffset);
  j.add("type", TopType2Json(m->getType(), taboffset + 2));
  if (!m->getModParams().empty()) {
    j.add("modparams", Params2Json(m->getModParams()));
  }
  if (!onlyDecl) {
    if (!m->getDefaultModArgs().empty()) {
      j.add("defaultmodargs", Values2Json(m->getDefaultModArgs()));
    }
    if (m->hasDef()) {
      ModuleDef* def = m->getDef();
      if (!def->getInstances().empty()) {
        auto insts = def->getInstances();
        j.add("instances", Instances2Json(insts, taboffset + 2));
      }
      if (!def->getConnections().empty()) {
        j.add("connections", Connections2Json(def, taboffset + 2));
      }
    }
    if (m->hasMetaData()) { j.add("metadata", toString(m->getMetaData())); }
  }
  if (m->hasDefaultLinkedModule()) {
    auto linked = m->getDefaultLinkedModule();
    auto ref_name = quote(linked->getRefName());
    j.add("default_linked_module", ref_name);
  }
  const auto linked = m->getLinkedModules();
  if (linked.size() > 0) {
    Dict linked_json(taboffset + 2);
    for (const auto& entry : linked) {
      auto ref_name = quote(entry.second->getRefName());
      linked_json.add(entry.first, ref_name);
    }
    j.add("linked_modules", linked_json.toMultiString());
  }
  return j.toMultiString();
}

string GeneratedModule2Json(Module* m, bool onlyDecl=false) {
  Array gm(10);
  gm.add(Values2Json(m->getGenArgs()));
  gm.add(Module2Json(m, onlyDecl));
  return gm.toMultiString();
}

string Generator2Json(Generator* g) {
  Dict j(6);
  j.add(
    "typegen",
    quote(
      g->getTypeGen()->getNamespace()->getName() + "." +
      g->getTypeGen()->getName()));
  j.add("genparams", Params2Json(g->getGenParams()));
  auto genmods = g->getGeneratedModules();
  if (!genmods.empty()) {
    Array gms(8);
    for (auto genmodp : genmods) {
      Module* m = genmodp.second;
      Array gm;
      gm.add(Values2Json(m->getGenArgs()));
      gm.add(Module2Json(m));
      gms.add(gm.toString());
    }
    j.add("modules", gms.toMultiString());
  }
  if (!g->getDefaultGenArgs().empty()) {
    j.add("defaultgenargs", Values2Json(g->getDefaultGenArgs()));
  }
  if (g->hasMetaData()) { j.add("metadata", toString(g->getMetaData())); }
  return j.toMultiString();
}

} // end namespace

void GeneratorJson::add_module(Module* m, bool onlyDecl=false) {
  ASSERT(m->isGenerated() && m->getGenerator() == this->g, "Module not generated from generator");
  modules.push_back(GeneratedModule2Json(m, onlyDecl));
}

string GeneratorJson::serialize() {
  Dict j(6);
  j.add(
    "typegen",
    quote(
      this->g->getTypeGen()->getNamespace()->getName() + "." +
      this->g->getTypeGen()->getName()));
  j.add("genparams", Params2Json(this->g->getGenParams()));
  Array gms(8);
  for (auto mjson : this->modules) {
    gms.add(mjson);
  }
  j.add("modules", gms.toMultiString());
  return j.toMultiString();
}

void TypeGenJson::add_type(Values v, Type* t) {
  this->types.emplace(Values2Json(v), Type2Json(t));
}

string TypeGenJson::serialize() {
  Array jtypegen(6);
  jtypegen.add(Params2Json(this->tg->getParams()));
  jtypegen.add(quote("sparse"));
  Array jsparselist(8);
  for (auto &[v, t] : this->types) {
    Array jvtpair;
    jvtpair.add(v);
    jvtpair.add(t);
    jsparselist.add(jvtpair.toString());
  }
  jtypegen.add(jsparselist.toMultiString());
  return jtypegen.toMultiString();
}

void NamespaceJson::add_module(Module* m, bool onlyDecl=false) {
  ASSERT(m->getNamespace() == this->ns, "Module not part of namespace");
  if (m->isGenerated()) {
    auto g = m->getGenerator();
    auto gname = g->getName();
    if (this->generators.count(gname) == 0) {
      this->generators.emplace(g->getName(), g);
    }
    this->generators.at(gname).add_module(m);
  }
  else {
    ASSERT(this->modules.count(m->getName())==0, "Already added module");
    this->modules.emplace(m->getName(), Module2Json(m, onlyDecl));
  }
}

TypeGenJson& NamespaceJson::getOrCreateTypeGen(TypeGen* tg) {
  auto& name = tg->getName();
  if (typegens.count(name) == 0) {
    this->typegens.emplace(name, tg);
  }
  return this->typegens.at(name);
}

string NamespaceJson::serialize() {
  Dict jns(2);

  //Add Modules first
  if (!this->modules.empty()) {
    Dict jmod(4);
    for (auto &[mname, mjson] : this->modules) {
      jmod.add(mname, mjson);
    }
    jns.add("modules", jmod.toMultiString());
  }

  //Add Generators next
  if (!this->generators.empty()) {
    Dict jgen(4);
    for (auto &[gname, gjson] : this->generators) {
      jgen.add(gname, gjson.serialize());
    }
    jns.add("generators", jgen.toMultiString());
  }

  //Add TypeGens last
  if (!this->typegens.empty()) {
    Dict jtypegens(4);
    // Spit out all of the cached types.
    for (auto &[tgname, tgjson] : this->typegens) {
      jtypegens.add(tgname, tgjson.serialize());
    }
    jns.add("typegens", jtypegens.toMultiString());
  }
  return jns.toMultiString();
}

//Original
std::string CoreIR::JsonLib::ns2Json(Namespace* ns) {
  auto modlist = ns->getModules(false);
  Dict jns(2);
  if (!modlist.empty()) {
    Dict jmod(4);
    for (auto m : modlist) {
      string mname = m.first;
      if (m.second->isGenerated()) mname = m.second->getGenerator()->getName();
      jmod.add(mname, Module2Json(m.second));
    }
    if (!jmod.isEmpty()) { jns.add("modules", jmod.toMultiString()); }
  }
  if (!ns->getGenerators().empty()) {
    Dict jgen(4);
    for (auto g : ns->getGenerators())
      jgen.add(g.first, Generator2Json(g.second));
    jns.add("generators", jgen.toMultiString());
  }
  if (!ns->getTypeGens().empty()) {
    Dict jtypegens(4);
    // Spit out all of the cached types.
    for (auto tgpair : ns->getTypeGens()) {
      string tgname = tgpair.first;
      TypeGen* tg = tgpair.second;
      Array jtypegen;
      jtypegen.add(Params2Json(tg->getParams()));
      if (tg->getCached().size() == 0) { jtypegen.add(quote("implicit")); }
      else {
        jtypegen.add(quote("sparse"));
        Array jsparselist(6);
        for (auto vtpair : tg->getCached()) {
          Array jvtpair;
          jvtpair.add(Values2Json(vtpair.first));
          jvtpair.add(Type2Json(vtpair.second));
          jsparselist.add(jvtpair.toString());
        }
        jtypegen.add(jsparselist.toMultiString());
      }
      jtypegens.add(tgname, jtypegen.toString());
    }
    jns.add("typegens", jtypegens.toMultiString());
  }
  return jns.toMultiString();
}
