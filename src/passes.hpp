#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "common.hpp"
#include "context.hpp"

void typecheck(Context* c, Module* m, bool* err);
void rungenerators(Context* c, Module* m, bool* err);

#endif //PASSES_HPP_
