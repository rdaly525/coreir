#ifndef COREIR_H_
#define COREIR_H_

#ifdef __cplusplus  // C++ header
#include "ir/casting/casting.h"
#include "ir/common.h"
#include "ir/constructor.h"
#include "ir/context.h"
#include "ir/coreirlib.h"
#include "ir/generator.h"
#include "ir/module.h"
#include "ir/moduledef.h"
#include "ir/namespace.h"
#include "ir/typegen.h"
#include "ir/types.h"
#include "ir/value.h"
#include "ir/valuetype.h"
#include "ir/wireable.h"

#include "ir/error.h"

#include "ir/directedview.h"
#include "ir/instancegraph.h"
#include "ir/passes.h"
#include "ir/passmanager.h"

#include "utils/util.h"

#else  // C header

#include "coreir-c/coreir.h"

#endif

#endif  // COREIR_H_
