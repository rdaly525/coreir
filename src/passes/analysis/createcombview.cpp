#include "coreir.h"
#include "coreir/passes/analysis/createcombview.h"

using namespace std;
using namespace CoreIR;

void Passes::CreateCombView::setupCoreir(Module* m) {
  string mname = m->getName();
  if (mname == "reg" || mname == "regRst") {
    srcs[m].insert({"out"});
    snks[m].insert({"in"});
    snks[m].insert({"clk"});
  }
  else if (mname == "mem") {
    for (auto record : m->getType()->getRecord()) {
      if (record.second->isInput()) {
        snks[m].insert({record.first});
      }
      else {
        assert(record.second->isOutput());
        srcs[m].insert({record.first});
      }
    }
  }
  else {
    set<SelectPath> inputs;
    set<SelectPath> outputs;
    for (auto record : m->getType()->getRecord()) {
      if (record.second->isInput()) {
        inputs.insert({record.first});
      }
      else {
        assert(record.second->isOutput());
        outputs.insert({record.first});
      }
    }
    combs[m].inputs = inputs;
    combs[m].outputs = outputs;
  }
}

void Passes::CreateCombView::setupCorebit(Module* m) {
  string mname = m->getName();
  if (mname == "reg") {
    srcs[m].insert({"out"});
    snks[m].insert({"in"});
    snks[m].insert({"clk"});
  }
  else {
    set<SelectPath> inputs;
    set<SelectPath> outputs;
    for (auto record : m->getType()->getRecord()) {
      if (record.second->isInput()) {
        inputs.insert({record.first});
      }
      else {
        assert(record.second->isOutput());
        outputs.insert({record.first});
      }
    }
    combs[m].inputs = inputs;
    combs[m].outputs = outputs;
  }
}


string Passes::CreateCombView::ID = "createcombview";
bool Passes::CreateCombView::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* m = node.getModule();
  if (m->getNamespace()->getName() == "coreir") {
    //Set srcs/snks/comb for coreir
    setupCoreir(m);
    return false;
  }
  if (m->getNamespace()->getName() == "corebit") {
    setupCorebit(m);
    return false;
  }
  ASSERT(m->hasDef(), "NEEDS Def! " + m->getRefName());
  ModuleDef* mdef = m->getDef();

  DirectedModule dm(m);

  map<Wireable*,Output*> outputInfo;
  map<Wireable*,Input*> inputInfo;
  
  for (auto outcon : dm.getOutputs()) {
    Wireable* output = outcon->getSnkWireable();
    assert(output->getType()->isInput()); //because reversed
    outputInfo.emplace(output,new Output());
  }
  
  for (auto incon : dm.getInputs()) {
    Wireable* input = incon->getSrcWireable();
    assert(input->getType()->isOutput());
    inputInfo.emplace(input,new Input());
  }
  
  //Find all combinational dependencies
  for (auto outcon : dm.getOutputs()) {
    Wireable* output = outcon->getSnkWireable();
    Wireable* con = outcon->getSrcWireable();
    traverseOut2In(con,output,outputInfo,inputInfo);
  }
  
  //All the outputs with no comb dependencies come from state. (not quite true, but good enough)
  for (auto outcon : dm.getOutputs()) {
    Wireable* output = outcon->getSnkWireable();
    if (outputInfo[output]->inputs.size()==0) {
      outputInfo[output]->states.insert(output); //Not sure why I am adding this here
    }
  }

  //Find all the inputs that are driving the next state
  
  //TODO for now I am just setting it to be all the inputs
  for (auto ipair : inputInfo) {
    if (ipair.second->outputs.size()==0) {
      ipair.second->states.insert(mdef->getInterface()); //TODO actually calculate this
    }
  }

  //for (auto ipair : mdef->getInstances()) {
  //  Module* mref = ipair->getModuleRef();
  //  if (!this->hasSrc(mref)) continue;
  //  for (auto 
  //}


  for (auto opair : outputInfo) {


    Output* oinfo = opair.second;
    Wireable* out = opair.first;
    SelectPath opath = out->getSelectPath();
    assert(opath[0]=="self");
    opath.pop_front();
    if (oinfo->states.size()>0) {
      srcs[m].insert(opath);
    }
    for (auto in : oinfo->inputs) {
      SelectPath ipath = in->getSelectPath();
      assert(ipath[0]=="self");
      ipath.pop_front();
      combs[m].inputs.insert(ipath);
      combs[m].outputs.insert(opath);
    }
  }

  for (auto ipair : inputInfo) {
    Input* iinfo = ipair.second;
    Wireable* in = ipair.first;
    if (iinfo->states.size()>0) {
      SelectPath ipath = in->getSelectPath();
      assert(ipath[0]=="self");
      ipath.pop_front();
      snks[m].insert(ipath);
    }
  }
  
  //cleanup
  for (auto opair : outputInfo) delete opair.second;
  for (auto ipair : inputInfo) delete ipair.second;
  
  return false;
}

void Passes::CreateCombView::traverseOut2In(Wireable* curin, Wireable* out, map<Wireable*,Output*>& outputInfo, map<Wireable*,Input*>& inputInfo) {
  assert(curin->getType()->isOutput());
  Wireable* parent = curin->getTopParent();
  if (isa<Interface>(parent)) {
    assert(outputInfo.count(out));
    outputInfo[out]->inputs.insert(curin);
    assert(inputInfo.count(curin));
    inputInfo[curin]->outputs.insert(out);
    return;
  }
  Instance* inode = cast<Instance>(parent);
  Module* mnode = inode->getModuleRef();
  if (this->hasComb(mnode)) {
    auto checkoutputs = combs[mnode].outputs;
    bool found = false;
    for (auto opath : checkoutputs) {
      for (auto spair : curin->getAllSelects()) {
        SelectPath spath = spair.second->getSelectPath();
        spath.pop_front();
        if (opath == spath) found = true;
      }
      for (auto spair : curin->getAllParents()) {
        SelectPath spath = spair.second->getSelectPath();
        spath.pop_front();
        if (opath == spath) found = true;
      }
    }
    if (!found) return;


    //TODO check that input is in checkoutputs
    for (auto nextpath : combs[mnode].inputs) {
      assert(inode->canSel(nextpath));
      Wireable* nextin = inode->sel(nextpath);
      for (auto con : nextin->getLocalConnections()) {
        traverseOut2In(con.second, out,outputInfo,inputInfo);
      }
    }
  }

}
