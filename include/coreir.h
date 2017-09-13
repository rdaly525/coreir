#ifndef COREIR_H_
#define COREIR_H_

#ifdef __cplusplus //C++ header
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/args.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/instantiable.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/wireable.h"

#include "coreir/ir/error.h"

#include "coreir/ir/directedview.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/passes.h"
#include "coreir/ir/instancegraph.h"

#else //C header

//#include "coreir-c/coreir.h"
//#include "fuck.h"

#endif



#endif //COREIR_H_
