#ifndef FIRRTL_HPP_
#define FIRRTL_HPP_

#include "coreir.h"

using namespace CoreIR;

class Firrtl : public InstanceGraphPass {
  unordered_map<Instantiable*,string> nameMap;
  vector<string> fmods;
  public :
    Firrtl() : InstanceGraphPass() {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node);
    void print();
};

#endif
