#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "common.hpp"
#include "context.hpp"

bool typecheck(CoreIRContext* c, Module* m);
bool rungenerators(CoreIRContext* c, Module* m);


#endif //PASSES_HPP_
