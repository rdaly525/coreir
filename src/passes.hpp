#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "common.hpp"
#include "context.hpp"

bool typecheck(Context* c, Module* m);
bool rungenerators(Context* c, Module* m);

#endif //PASSES_HPP_
