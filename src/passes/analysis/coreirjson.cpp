#include "coreir.h"
#include "coreir/passes/analysis/coreirjson.h"
#include <set>
#include <map>

using namespace CoreIR;
using namespace std;
namespace {
typedef vector<std::pair<string,string>> VStringPair;

string tab(uint s) {
  string ret = "";
  for (uint i=0; i<s; ++i) {
    ret += " ";
  }
  return ret;
}
string quote(string s) {
  return "\""+s+"\"";
}

class Dict {
  string ts="";
  vector<string> fields;
  map<string,string> sorted;
  public:
    Dict(uint i) : ts(tab(i)) {}
    Dict() {}
    bool isEmpty() { return fields.size()==0;}
    void add(string field,string val) { 
      fields.push_back(quote(field)+":"+val);
      sorted[field] = quote(field)+":"+val;
    }
    string toMultiString(bool sort=false) {
      if (sort) {
        fields.clear();
        for (auto fmap : sorted) {
          fields.push_back(fmap.second);
        }
      }
      return "{\n" + ts + "  " + join(fields.begin(),fields.end(),",\n"+ts+"  ") + "\n"+ts+"}";
    }
    string toString() {
      return "{"+join(fields.begin(),fields.end(),string(", ")) + "}";
    }

};

class Array {
  string ts="";
  vector<string> fields;
  public:
    Array(uint i) : ts(tab(i)) {}
    Array() {}
    void add(string field) { fields.push_back(field);}
    string toString() {
      return "[" + join(fields.begin(),fields.end(),string(",")) + "]";
    }
    string toMultiString() {
      return "[\n" + ts + "  " + join(fields.begin(),fields.end(),",\n"+ts+"  ") + "\n"+ts+"]";
    }
};


string ValueType2Json(ValueType* vt) {
  if (auto bvt = dyn_cast<BitVectorType>(vt)) {
    Array a;
    a.add(quote("BitVector"));
    a.add(to_string(bvt->getWidth()));
    return a.toString();
  }
  return quote(vt->toString());
}

//Ordere these in order as well
string Params2Json(Params gp) {
  Dict j;
  for (auto it : gp) j.add(it.first,ValueType2Json(it.second));
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
      ASSERT(0,"NYI");
    }
  }
  else {
    ASSERT(0,"NYI");
  }
  return ret.toString();
}

string Values2Json(Values vs) {
  Dict j;
  for (auto it : vs) j.add(it.first,Value2Json(it.second));
  return j.toString();
}

string TopType2Json(Type* t,int taboffset) {
  ASSERT(isa<RecordType>(t),"Expecting Record type but got " + t->toString());
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

//One Line
string Type2Json(Type* t) {
  if (isa<BitType>(t)) return quote("Bit");
  if (isa<BitInType>(t)) return quote("BitIn");

  if (isa<BitInOutType>(t)) {
    return quote("BitInOut");
  }
  Array a;
  if (auto nt = dyn_cast<NamedType>(t)) {
    a.add(quote("Named"));
    a.add(quote(nt->getNamespace()->getName() + "." + nt->getName()));
  }
  else if(auto at = dyn_cast<ArrayType>(t)) {
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

string Instances2Json(map<string,Instance*>& insts,int taboffset) {
  Dict jis(taboffset);
  for (auto imap : insts) {
    string iname = imap.first;
    Instance* i = imap.second;
    Dict j(taboffset+2);
    Module* m = i->getModuleRef();
    if (m->isGenerated()) {
      j.add("genref",quote(m->getGenerator()->getRefName()));
      j.add("genargs",Values2Json(m->getGenArgs()));
    }
    else {
      j.add("modref",quote(i->getModuleRef()->getNamespace()->getName() + "." + i->getModuleRef()->getName()));
    }
    if (i->hasModArgs()) {
      j.add("modargs",Values2Json(i->getModArgs()));
    }
    if (i->hasMetaData()) {
      j.add("metadata",toString(i->getMetaData()));
    }
    jis.add(iname,j.toMultiString());
  }
  return jis.toMultiString();
}

string Connections2Json(Connections& cons,int taboffset) {
  Array a(taboffset);
  vector<Connection> sortedConns;
  for (auto c : cons) {
    sortedConns.push_back(c);
  }

  // Ensure that connections are serialized in select string sorted order
  ConnectionStrComp c;
  std::sort(begin(sortedConns), end(sortedConns), [c](const Connection& l, const Connection& r) {
      return c(l, r);
    });

  for (auto con : sortedConns) {
    auto pa = con.first->getSelectPath();
    auto pb = con.second->getSelectPath();
    string sa = join(pa.begin(),pa.end(),string("."));
    string sb = join(pb.begin(),pb.end(),string("."));
    Array b;
    if (sa > sb) {
      b.add(quote(sa));
      b.add(quote(sb));
    }
    else {
      b.add(quote(sb));
      b.add(quote(sa));
    }
    a.add(b.toString());
  }
  return a.toMultiString();
}

string Module2Json(Module* m, int taboffset) {
  Dict j(taboffset);
  j.add("type",TopType2Json(m->getType(),taboffset+2));
  if (!m->getModParams().empty()) {
    j.add("modparams",Params2Json(m->getModParams()));
  }
  if (!m->getDefaultModArgs().empty()) {
    j.add("defaultmodargs",Values2Json(m->getDefaultModArgs()));
  }
  if (m->hasDef()) {
    ModuleDef* def = m->getDef();
    if (!def->getInstances().empty()) {
      auto insts = def->getInstances();
      j.add("instances",Instances2Json(insts, taboffset+2));
    }
    if (!def->getConnections().empty()) {
      auto cons = def->getConnections();
      j.add("connections",Connections2Json(cons,taboffset+2));
    }
  }
  if (m->hasMetaData()) {
    j.add("metadata",toString(m->getMetaData()));
  }
  return j.toMultiString();
}

Json Generator2Json(Generator* g) {
  Dict j(6);
  j.add("typegen",quote(g->getTypeGen()->getNamespace()->getName() + "."+g->getTypeGen()->getName()));
  j.add("genparams",Params2Json(g->getGenParams()));
  auto genmods = g->getGeneratedModules();
  if (!genmods.empty()) {
    Array gms(8);
    for (auto genmodp : genmods) {
      Module* m = genmodp.second;
      Array gm;
      gm.add(Values2Json(m->getGenArgs()));
      gm.add(Module2Json(m,10));
      gms.add(gm.toString());
    }
    j.add("modules",gms.toMultiString());
  }
  if (!g->getDefaultGenArgs().empty()) {
    j.add("defaultgenargs",Values2Json(g->getDefaultGenArgs()));
  }
  if (g->hasMetaData()) {
    j.add("metadata",toString(g->getMetaData()));
  }
  return j.toMultiString();
}
}//anonomous namespace

string Passes::CoreIRJson::ID = "coreirjson";
bool Passes::CoreIRJson::runOnNamespace(Namespace* ns) {
  Dict jns(2);
  auto modlist = ns->getModules(false);
  if (!modlist.empty()) {
    Dict jmod(4);
    for (auto m : modlist) {
      string mname = m.first;
      if (m.second->isGenerated()) mname = m.second->getGenerator()->getName();
      jmod.add(mname,Module2Json(m.second,6));
    }
    if (!jmod.isEmpty()) {
      jns.add("modules",jmod.toMultiString());
    }
  }
  if (!ns->getGenerators().empty()) {
    Dict jgen(4);
    for (auto g : ns->getGenerators()) jgen.add(g.first,Generator2Json(g.second));
    jns.add("generators",jgen.toMultiString());
  }
  //if (!namedTypeNameMap.empty()) {
  //  ASSERT(0,"NYI");
    //Dict jntypes;
    //for (auto nPair : namedTypeNameMap) {
    //  string n = nPair.first;
    //  string nFlip = nPair.second;
    //  NamedType* nt = namedTypeList.at(n);
    //  Type* raw = nt->getRaw();
    //  json jntype = {
    //    {"flippedname",nFlip},
    //    {"rawtype", raw->toJson()}
    //  };
    //  jntypes[n] = jntype;
    //}
    //j["namedtypes"] = jntypes;
  //} 
  if (!ns->getTypeGens().empty()) {
    Dict jtypegens(4);
    //Spit out all of the cached types.
    for (auto tgpair : ns->getTypeGens()) {
      string tgname = tgpair.first;
      TypeGen* tg = tgpair.second;
      Array jtypegen;
      jtypegen.add(Params2Json(tg->getParams()));
      if (tg->getCached().size()==0) {
        jtypegen.add(quote("implicit"));
      }
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
      jtypegens.add(tgname,jtypegen.toString());
    }
    jns.add("typegens",jtypegens.toMultiString());
  }
  nsMap[ns->getName()] = jns.toMultiString();
  return false;
}


void Passes::CoreIRJson::writeToStream(std::ostream& os,string topRef) {
  os << "{";
  if (topRef!="") {
    os << quote("top") << ":" << quote(topRef) << ",";
  }
  os << endl;
  Dict jn(0);
  for (auto nmap : nsMap) {
    jn.add(nmap.first,nmap.second);
  }
  os << quote("namespaces") << ":" << jn.toMultiString();
  os << endl << "}";
}

