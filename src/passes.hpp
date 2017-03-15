#ifndef PASSES_HPP_
#define PASSES_HPP_


#include "common.hpp"
#include "context.hpp"

namespace CoreIR {

void typecheck(Context* c, Module* m, bool* err);
void rungenerators(Context* c, Module* m, bool* err);

}//CoreIR namespace

#endif //PASSES_HPP_
