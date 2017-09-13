#ifndef REMOVEBULKCONNECTIONS_HPP_
#define REMOVEBULKCONNECTIONS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {


class RemoveBulkConnections : public ModulePass {
  public :
    static std::string ID;
    
    RemoveBulkConnections() : ModulePass(ID,"Removes any bulk connections. Only connections will be bits and arrays of bits") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
