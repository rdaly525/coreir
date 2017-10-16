#include "coreir.h"
#include "coreir/passes/analysis/firrtl.h"

using namespace std;
using namespace CoreIR;

string toFConst(BitVector bv) {
  return "UInt<"+to_string(bv.bitLength())+">(" + to_string(bv.to_type<uint64_t>()) + ")";
}
string toFConst(int i) {
  return "UInt(" + to_string(i) + ")";
}


string CoreIR::Passes::FModule::type2firrtl(Type* t, bool isInput) {
  if (auto rt = dyn_cast<RecordType>(t)) {
    vector<string> sels;
    if (!rt->isMixed()) {
      for (auto rec : rt->getRecord()) {
        sels.push_back(rec.first + " : " + type2firrtl(rec.second,isInput));
      }
    }
    else {
      ASSERT(0,"NYI");
    }
    return join(sels.begin(),sels.end(),string(", "));
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    Type* et = at->getElemType();
    if (et->isBaseType()) {
      return "UInt<" + to_string(at->getLen()) + ">";
    }
    else {
      return type2firrtl(et,isInput) + "[" + to_string(at->getLen()) + "]";
    }
  }
  else if (auto nt = dyn_cast<NamedType>(t)) {
    if (nt == c->Named("coreir.clk") || nt == c->Named("coreir.clkIn")) return "Clock";
    else if (nt == c->Named("coreir.rst") || nt == c->Named("coreir.rstIn")) return "UInt<1>";
    else ASSERT(0,"NYI: " + nt->toString());
  }
  else if (t->isBaseType()) {
    return "UInt<1>";
  }
  else {
    ASSERT(0,"DEBUGME: " +t->toString());
  }
}

string sp2Str(SelectPath sp) {
  string ret = sp[0];
  sp.pop_front();
  for (auto s : sp) {
    if (isNumber(s)) ret  = ret +"[" + s + "]";
    else ret = ret + "." + s;
  }
  return ret;
}

void addConnection(Context* c,CoreIR::Passes::FModule* fm, SelectPath snk, SelectPath src) {
  string snkstr = sp2Str(snk);
  if (!isNumber(src.back())) {
    fm->addStmt(snkstr + " <= " + sp2Str(src));
  }
  else if (src.size()==3) {
    SelectPath tsrc = src;
    tsrc.pop_back();
    string tname = "tmpidx" + c->getUnique();
    fm->addStmt("wire " + tname + " : UInt");
    fm->addStmt(tname + " <= bits(" + sp2Str(tsrc)+","+src.back() + "," + src.back() + ")");
    fm->addStmt(snkstr + " <= " + tname);
  }
}

//TODO find a regex lib
void searchAndReplace(string& val, string s, string r) {
  ASSERT(0,"NYI");
}


string CoreIR::Passes::FModule::toString() {
  vector<string> lines;
  lines.push_back("  module " + this->name + " :");
  for (auto s : this->io) {
    lines.push_back("    " + s);
  }
  for (auto s : this->stmts) {
    lines.push_back("    " + s);
  }
  string ret = join(lines.begin(),lines.end(),string("\n"));
  if (gparams.size()) {
    for (auto p : gparams) {
      assert(0);
      //searchAndReplace(ret,p,p);
    }
  }
  return ret;
}





string Passes::Firrtl::ID = "firrtl";
bool Passes::Firrtl::runOnInstanceGraphNode(InstanceGraphNode& node) {
  auto i = node.getInstantiable();
  Module* m = cast<Module>(i);
  auto fm = new FModule(m);
  ASSERT(modMap.count(m)==0,"DEBUGME");
  this->modMap[m] = fm;
  this->fmods.push_back(fm);
  
  ASSERT(fm->hasDef(),"NYI external modules: " + fm->getName() + " : " + m->toString());
  if (!m->hasDef()) return false;
  ModuleDef* def = m->getDef();
  
  //First add all instances
  for (auto instpair : def->getInstances()) {
    Instance* inst = instpair.second;
    string iname = instpair.first;
    Module* mref = inst->getModuleRef();
    ASSERT(modMap.count(mref),"DEBUGMEs");
    FModule* fmref = modMap[mref];
    fm->addStmt("inst " + iname + " of " + fmref->getName());
    //This will set all modArgs as inputs to the module
    if (inst->getModArgs().size()) {
      for (auto vpair : inst->getModArgs()) {
        string p = vpair.first;
        Value* v = vpair.second;
        string stmt = iname + "." + p + " <= ";
        if (auto av = dyn_cast<Arg>(v)) {
          stmt = stmt + av->getField();
        }
        else if (auto aint = dyn_cast<ConstInt>(v)) {
          stmt = stmt + toFConst(aint->get());
        }
        else if (auto abv = dyn_cast<ConstBitVector>(v)) {
          stmt = stmt + toFConst(abv->get());
        }
        else {
          ASSERT(0,"NYI: Value " +p+ " cannot be " + v->toString());
        }
        fm->addStmt(stmt);
      }
    }
  }
  //Then add all connections
  auto dm = m->newDirectedModule();
  for (auto dcon : dm->getConnections()) {
    SelectPath src = dcon->getSrc();
    if (src[0] == "self") src.pop_front();
    SelectPath snk = dcon->getSnk();
    ASSERT(snk.size()<3,"NYI setting to indexed thing");
    if (snk[0] == "self") snk.pop_front();
    addConnection(getContext(),fm,snk,src);
  }
  return false;
}

void Passes::Firrtl::writeToStream(std::ostream& os) {
  Module* top = getContext()->getTop();
  ASSERT(top, "Firrtl requires a top module");
  ASSERT(modMap.count(top),"DEBUGME");
  os << "circuit " + modMap[top]->getName() + " : " << endl;
  for (auto fm : fmods) {
    os << fm->toString() << endl;
  }
}






