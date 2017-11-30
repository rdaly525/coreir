#include "coreir.h"
#include "coreir/passes/transform/transform2combview.h"

#include "coreir/passes/analysis/createcombview.h"

using namespace std;
using namespace CoreIR;

namespace {
struct Helper {
  Context* c;
  map<string,Helper*> selects;
  Type* type = nullptr;
  Helper(Context* c) : c(c) {}
  ~Helper() {
    for (auto h : selects) {
      delete h.second;
    }
  }
  Type* getType() {
    if (type) return type;
    assert(selects.size()>0);
    if (isNumber(selects.begin()->first)) {
      int max = -1;
      set<uint> nums;
      Type* elemtype = selects.begin()->second->getType();
      for (auto spair : selects) {
        assert(isNumber(spair.first));
        Type* checktype = spair.second->getType();
        assert(checktype == elemtype);
        int i = stoi(spair.first);
        nums.insert(i);
        if (i>max) max = i;
      }
      for (int i=0; i<=max; ++i) {
        assert(nums.count(i)>0);
      }
      this->type = c->Array(max+1,elemtype);
      return this->type;
    }
    else { //Is a record
      RecordParams rps;
      for (auto spair : selects) {
        rps.push_back({spair.first,spair.second->getType()});
      }
      this->type = c->Record(rps);
      return this->type;
    }
  }
  void addPath(SelectPath path,Type* t) {
    if (path.size()==0) {
      this->type = t;
      return;
    }
    string sel = path.front();
    assert(t->canSel(sel));
    if (selects.count(sel)==0) {
      selects[sel] = new Helper(c);
    }
    path.pop_front();
    selects[sel]->addPath(path,t->sel(sel));
  }

};

RecordType* createType(Context* c,RecordType* mtype,set<SelectPath>& paths) {
  Helper* h = new Helper(c);
  for (auto path : paths) {
    assert(mtype->canSel(path));
    h->addPath(path,mtype);
  }
  RecordType* ret = cast<RecordType>(h->getType());
  delete h;
  return ret;
}

void connect(ModuleDef* def, SelectPath path, string ptname, string iname) {
  SelectPath ptpath = path;
  ptpath.push_front("in");
  ptpath.push_front(ptname);

  SelectPath snkpath = path;
  snkpath.push_front(iname);
  def->connect(ptpath,snkpath);
}


}

string Passes::Transform2CombView::ID = "transform2combview";
bool Passes::Transform2CombView::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Context* c = getContext();
  Module* m = node.getModule();
  
  if (node.getInstanceList().size() == 0) {
    return false;
  }
  
  RecordType* mtype = m->getType();
  Namespace* ns = m->getNamespace();
  auto combview = getAnalysisPass<CreateCombView>();
  
  string mname = m->getLongName();
  string mname_src = mname+"_src";
  string mname_snk = mname+"_snk";
  string mname_comb = mname+"_comb";
  if (combview->hasSrc(m)) {
    //cout << "HEREsrc" << endl;
    RecordType* srctype = createType(c,mtype,combview->getSrc(m));
    auto newmod = ns->newModuleDecl(mname_src,srctype);
    newmod->getMetaData()["original"] = m->getRefName();
  }

  if (combview->hasSnk(m)) {
    //cout << "HEREsnk" << endl;
    RecordType* snktype = createType(c,mtype,combview->getSnk(m));
    auto newmod = ns->newModuleDecl(mname_snk,snktype);
    newmod->getMetaData()["original"] = m->getRefName();
  }
  
  if (combview->hasComb(m)) {
    //cout << "HEREcomb " << mname_comb << endl;
    set<SelectPath> combset = combview->getComb(m).inputs;
    set<SelectPath> combouts = combview->getComb(m).outputs;
    combset.insert(combouts.begin(),combouts.end());
    RecordType* combtype = createType(c,mtype,combset);
    auto newmod = ns->newModuleDecl(mname_comb,combtype);
    newmod->getMetaData()["original"] = m->getRefName();
  }


  for (auto inst : node.getInstanceList()) {
    ModuleDef* def = inst->getContainer();
    string ptname = "_pt" + getContext()->getUnique();
    auto pt = addPassthrough(inst,ptname);
    string iname = inst->getInstname();
    string iname_src = iname + "_src";
    string iname_snk = iname + "_snk";
    string iname_comb = iname + "_comb";

    //inst is now freed
    def->removeInstance(inst);
   
    //Add new instances
    if (combview->hasSrc(m)) {
      auto newinst = def->addInstance(iname_src,ns->getModule(mname_src));
      newinst->getMetaData()["srcsnkcomb"] = "src";
      newinst->getMetaData()["original"] = iname;
    }
    if (combview->hasSnk(m)) {
      auto newinst = def->addInstance(iname_snk,ns->getModule(mname_snk));
      newinst->getMetaData()["srcsnkcomb"] = "snk";
      newinst->getMetaData()["original"] = iname;
    }
    if (combview->hasComb(m)) {
      auto newinst = def->addInstance(iname_comb,ns->getModule(mname_comb));
      newinst->getMetaData()["srcsnkcomb"] = "comb";
      newinst->getMetaData()["original"] = iname;
    }

    //Src
    for (auto path : combview->getSrc(m)) {
      connect(def,path,ptname,iname_src);
    }
    
    //Snk
    for (auto path : combview->getSnk(m)) {
      connect(def,path,ptname,iname_snk);
    }

    //Comb inputs
    for (auto path : combview->getComb(m).inputs) {
      connect(def,path,ptname,iname_comb);
    }

    //Comb outputs 
    for (auto path : combview->getComb(m).outputs) {
      connect(def,path,ptname,iname_comb);
    }
    
    //inline passthrough
    inlineInstance(pt);

  }
  return true;
}


