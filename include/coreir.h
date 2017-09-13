#ifndef COREIR_H_
#define COREIR_H_

#ifdef __cplusplus //C++ header
#include "coreir/ir/casting/casting.hpp"
#include "coreir/ir/common.hpp"
#include "coreir/ir/context.hpp"
#include "coreir/ir/namespace.hpp"
#include "coreir/ir/args.hpp"
#include "coreir/ir/types.hpp"
#include "coreir/ir/typegen.hpp"
#include "coreir/ir/instantiable.hpp"
#include "coreir/ir/moduledef.hpp"
#include "coreir/ir/wireable.hpp"

#include "coreir/ir/error.hpp"

#include "coreir/ir/directedview.hpp"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/passes.h"
#include "coreir/ir/instancegraph.h"

#else //C header

//#include "coreir-c/coreir.h"
//#include "fuck.h"

#endif



#endif //COREIR_H_
