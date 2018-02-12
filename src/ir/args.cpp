#include "coreir/ir/args.h"
#include "coreir/ir/value.h"

using namespace std;

namespace CoreIR {

Args::Args(Params params) {
  for (auto ppair : params) {
    assert(args.count(ppair.first)==0);
    args[ppair.first] = new Arg(ppair.second,ppair.first);
  }
}

Args::~Args() {
  for (auto apair : args) delete apair.second;
}

}
