#include "coreir.h"
#include "coreir/passes/transform/groupconnections.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::GroupConnections::ID = "groupconnections";
bool Passes::GroupConnections::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  ModuleDef* def = m->getDef();
  cout << "Connections" << endl;
  vector<Connection> arrayToArrayConns;
  for (auto& conn : def->getConnections()) {


    Wireable* l = conn.first;
    Wireable* r = conn.second;

    if (isa<Select>(l) && isa<Select>(r)) {
      Select* ls = cast<Select>(l);
      Select* rs = cast<Select>(r);

      if (isNumber(ls->getSelStr()) &&
          isNumber(rs->getSelStr())) {

        auto lsTp = cast<ArrayType>(ls->getParent()->getType());
        auto rsTp = cast<ArrayType>(rs->getParent()->getType());

        cout << ls->getParent()->toString() << " len = " << lsTp->getLen() << endl;
        cout << rs->getParent()->toString() << " len = " << rsTp->getLen() << endl;
        if (lsTp->getLen() == rsTp->getLen()) {
          arrayToArrayConns.push_back(conn);
          cout << "( " << ls->toString() << ", " << rs->toString() << " )" << endl;
        }
      }
    }
  }

  cout << "# of array - array connections = " << arrayToArrayConns.size() << endl;
  vector<vector<Connection> > cLists;
    
  return false;
}
