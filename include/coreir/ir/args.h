
#include "fwd_declare.h"

namespace CoreIR {
class Args {
  std::map<std::string,Arg*> args;
  protected :
    Args(Params params);
  public :
    ~Args();
    Arg* getArg(std::string field) {
      ASSERT(args.count(field),"Missing arg: " + field);
      return args[field];
    }
};

}
