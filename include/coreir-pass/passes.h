#ifndef PASSES_HPP_
#define PASSES_HPP_

#include "coreir.h"

namespace CoreIR {

void rungenerators(CoreIR::Context* c, CoreIR::Module* m, bool* err);
void flatten(CoreIR::Context* c, CoreIR::Module* m, bool* err);

//Inlines the instance
void inlineInstance(Instance*);

Instance* addPassthrough(Context* c, Wireable* w,string instname);


//Container: the module that will be modified.
//pattern: the module defines the interface and instances that it will match
//replacement: The Generator that will replace the pattern that was found
//configargs: configargs for the replacement TODO can I set these based off the found pattern?
//Returns if it modified container (Found a match)
bool matchAndReplace(Module* container, Module* pattern, Module* replacement, Args configargs);
bool matchAndReplace(Module* container, Module* pattern, Module* replacement,std::function<Args(const Instance*)> getConfigargs);

}
#endif //PASSES_HPP_
