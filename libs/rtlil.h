#ifndef COREIR_RTLIL_H_
#define COREIR_RTLIL_H_

#include "coreir-c/ctypes.h"
#include "common/common-macros.h"

#ifdef __cplusplus
#include "ir/coreir.h"
COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(rtlil);
#endif

COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(rtlil);

#endif  // COREIR_RTLIL_HPP_
