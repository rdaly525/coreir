//#include "coreir.h"

#include "../../include/coreir/ir/value.h"

using namespace CoreIR;
using namespace std;

int main() {
  
  ValuePtr a = Arg::make("bob");
  ValuePtr c = Const::make("bob");


  //shared_ptr<Expr> cb = new ConstBool(true);
  //cout << isa<Expr>(cb) << endl;
  //cout << isa<ConstBool>(cb) << endl;
  //cout << cast<ConstBool>(cb)->get() << endl;

  
  ////shared_ptr<Const> sc = shared_ptr<Const>(new IConst(5));
  ////assert(isa<Const>(sc));
  //shared_ptr<Expr> a = cast<Expr>(sc);
  //cout << a->eval<int>() << endl;
  //shared_ptr<IConst> ic = cast<IConst>(sc);
  //ic->bar();
  //shared_ptr<IConst> dc = dyn_cast<IConst>(sc);
  //dc->bar();
  //cout << "ROSS" << endl;
  ////shared_ptr<IConst> b = cast<IConst>(sc);
  //sc->foo();
 
  //
  //sc->foo();
  

  return 0;
}
