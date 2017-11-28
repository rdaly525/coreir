#include "coreir.h"
#include "coreir/passes/transform/transform2combview.h"

using namespace std;
using namespace CoreIR;

namespace {
void connect(ModuleDef* def, SelectPath path, string ptname, string mname) {
  SelectPath ptpath = path;
  ptpath.push_front("out");
  ptpath.push_front(ptname);

  SelectPath snkpath = path;
  snkpath.push_front(mname);
  def->connect(ptpath,snkpath);
}
}

string Passes::Transform2CombView::ID = "transform2combview";
bool Passes::Transform2CombView::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* m = node.getModule();
  RecordType* mtype = m->getType();
  Namespace* ns = m->getNamespace();
  auto combview = getAnalysisPass<CreateCombView>();
  
  string mname = m->getLongName();
  string mname_src = mname+"_src";
  string mname_snk = mname+"_snk";
  string mname_comb = mname+"_comb";
  if (combview->hasSrc(m)) {
    RecordType* srctype = createType(mtype,combview->getSrc(m));
    ns->newModuleDecl(mname_src,srctype);
  }

  if (combview->hasSnk(m)) {
    RecordType* snktype = createType(mtype,combview->getSnk(m));
    ns->newModuleDecl(mname_snk,snktype);
  }
  
  for (auto inst : node.getInstanceList()) {
    ModuleDef* def = inst->getContainer();
    ptname = "_pt" + getContext()->getUnique();
    auto pt = addPassthrough(inst,ptname);
    
    //inst is now freed
    def->removeInstance(inst);
    
    //Src
    for (auto path : combview->getSrc(m)) {
      connect(def,path,ptname,mname_snk);
    }
    
    //Snk
    for (auto path : combview->getSnk(m)) {
      connect(def,path,ptname,mname_snk);
    }

    //Comb inputs
    for (auto path : combview->getComb(m).first) {
      connect(def,path,ptname,mname_comb);
    }

    //Comb outputs 
    for (auto path : combview->getComb(m).second) {
      connect(def,path,ptname,mname_comb);
    }

    //inline passthrough
    inlineInstance(pt);

  }

}


