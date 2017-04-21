#ifndef TYPECHECK_HPP_
#define TYPECHECK_HPP_

#include "coreir.h"

namespace CoreIR {

//Will not modify graph
void typecheck(Context* c, Module* m, bool* err);

}//CoreIR namespace

#endif //TYPECHECK_HPP_
