#include "coreir.h"
#include "coreir/passes/analysis/coreirjson.h"
#include <set>
#include <map>

//TODO Write out Generator mod defs
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
    else if (auto at = dyn_cast<ConstCoreIRType>(con)) {
      ret.add(Type2Json(at->get()));
    }
    else if (auto at = dyn_cast<ConstModule>(con)) {
      ret.add(quote(at->get()->getRefName()));
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

string TopType2Json(Type* t) {
  ASSERT(isa<RecordType>(t),"Expecting Record type but got " + t->toString());
  Array a;
  a.add(quote("Record"));
  auto rt = cast<RecordType>(t);
  Array r(8);
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

string Instances2Json(map<string,Instance*>& insts) {
  Dict jis(8);
  //TODO maybe keep an insertion order for all the instances/Modules/Generators/Namespaces
  for (auto imap : insts) {
    string iname = imap.first;
    Instance* i = imap.second;
    Dict j(10);
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

string Connections2Json(Connections& cons) {
  Array a(8);
  for (auto con : cons) {
    auto pa = con.first->getSelectPath();
    auto pb = con.second->getSelectPath();
    string sa = join(pa.begin(),pa.end(),string("."));
    string sb = join(pb.begin(),pb.end(),string("."));
    Array b;
    b.add(quote(sa));
    b.add(quote(sb));
    a.add(b.toString());
  }
  return a.toMultiString();
}

string Module2Json(Module* m) {
  Dict j(6);
  if (m->hasDef() && m->isGenerated()) {
    j.add("genref",quote(m->getGenerator()->getRefName()));
    j.add("genargs",Values2Json(m->getGenArgs()));
  }
  j.add("type",TopType2Json(m->getType()));
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
      j.add("instances",Instances2Json(insts));
    }
    if (!def->getConnections().empty()) {
      auto cons = def->getConnections();
      j.add("connections",Connections2Json(cons));
    }
  }
  if (m->hasMetaData()) {
    j.add("metadata",toString(m->getMetaData()));
  }
  return j.toMultiString();
}

json Generator2Json(Generator* g) {
  Dict j(6);
  j.add("typegen",quote(g->getTypeGen()->getNamespace()->getName() + "."+g->getTypeGen()->getName()));
  j.add("genparams",Params2Json(g->getGenParams()));
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
  if (!ns->getModules().empty()) {
    Dict jmod(4);
    for (auto m : ns->getModules()) {
      string mname = m.first;
      if (m.second->isGenerated()) mname = m.second->getGenerator()->getName();
      if (m.second->isGenerated() && !m.second->hasDef()) continue;
      jmod.add(mname,Module2Json(m.second));
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
  //if (!typeGenNameMap.empty()) {
  //  ASSERT(0,"NYI");
    //json jntypegens;
    //for (auto nPair : typeGenNameMap) {
    //  string n = nPair.first;
    //  string nFlip = nPair.second;
    //  TypeGen* tg = typeGenList.at(n);
    //  json jntypegen = {
    //    {"genparams", Params2Json(tg->getParams())}
    //  };
    //  if (nFlip != "") {
    //    jntypegen["flippedname"] = nFlip;
    //  }
    //  jntypegens[n] = jntypegen;
    //}
    //j["namedtypegens"] = jntypegens;
  //}
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

