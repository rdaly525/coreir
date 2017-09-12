#ifndef COREIR_H_
#define COREIR_H_

#include "../src/ir/casting/casting.hpp"
#include "../src/ir/common.hpp"
#include "../src/ir/context.hpp"
#include "../src/ir/namespace.hpp"
#include "../src/ir/args.hpp"
#include "../src/ir/types.hpp"
#include "../src/ir/typegen.hpp"
#include "../src/ir/instantiable.hpp"
#include "../src/ir/moduledef.hpp"
#include "../src/ir/wireable.hpp"

#include "../src/ir/error.hpp"

#include "../src/ir/directedview.hpp"
#include "../src/ir/passmanager.h"
#include "../src/ir/passes.h"
#include "../src/ir/instancegraph.h"


namespace CoreIR {
//extra helper functions

//Inlines the instance
  bool inlineInstance(Instance*);
  Instance* addPassthrough(Wireable* w,std::string instname);
}

#endif //COREIR_H_
