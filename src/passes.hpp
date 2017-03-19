#ifndef PASSES_HPP_
#define PASSES_HPP_


#include "common.hpp"
#include "context.hpp"

namespace CoreIR {

//LLVM returns a bool whether it modified the graph
//Will modify graph
void rungenerators(Context* c, Module* m, bool* err);
void cgramapper(Context* c, Module* m, bool* err);

//Will not modify graph
void typecheck(Context* c, Module* m, bool* err);

}//CoreIR namespace

#endif //PASSES_HPP_
