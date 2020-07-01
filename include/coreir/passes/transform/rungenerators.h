#ifndef RUNGENERATORS_HPP_
#define RUNGENERATORS_HPP_

#include "coreir.h"
// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it

namespace CoreIR {
namespace Passes {

class RunGenerators : public ContextPass {
 public:
  RunGenerators() : ContextPass("rungenerators", "Runs all generators") {}
  bool runOnContext(Context* ns);
};

}  // namespace Passes
}  // namespace CoreIR

#endif
