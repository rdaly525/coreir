#ifndef STDLIB_H_
#define STDLIB_H_

//TODO Macrofy

#ifdef __cplusplus
#include "coreir.h"
CoreIR::Namespace* CoreIRLoadLibrary_stdlib(CoreIR::Context* c);
#else
#include "coreir-c/coreir.h"
extern CORENamespace* CORELoadLibrary_stdlib(COREContext* c);
#endif


#endif //STDLIB_HPP_
