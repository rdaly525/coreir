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

  cout << "Processing module: " << m->getName() << endl;

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

        //cout << ls->getParent()->toString() << " len = " << lsTp->getLen() << endl;
        //cout << rs->getParent()->toString() << " len = " << rsTp->getLen() << endl;
        if (lsTp->getLen() == rsTp->getLen()) {

          auto lParent = ls->getParent();
          auto rParent = rs->getParent();

          if (lParent < rParent) {
            arrayToArrayConns.push_back({ls, rs});
          } else {
            arrayToArrayConns.push_back({rs, ls});
          }
          //cout << "( " << ls->toString() << ", " << rs->toString() << " )" << endl;
        }
      }
    }
  }

  sort_lt(arrayToArrayConns, [](const Connection& l) {
      return stoi(cast<Select>(l.first)->getSelStr());
    });

  stable_sort(begin(arrayToArrayConns),
              end(arrayToArrayConns),
              [](const Connection& l,
                 const Connection& r) {
                return cast<Select>(l.first)->getParent() < cast<Select>(r.first)->getParent();
              });
  // sort_lt(arrayToArrayConns, [](const Connection& l) {
  //     return cast<Select>(l.first)->getParent();
  //   });

  cout << "--- Sorted connections" << endl;
  for (auto& conn : arrayToArrayConns) {
    cout << "( " << conn.first->toString() << ", " << conn.second->toString() << " )" << endl;
  }

  // Idea: Sort each pair so that the wireable with the lower value parent is
  // always on the lhs

  // Next: Sort the list of connections by lhs, then sort by rhs
  // 

  
  cout << "# of array - array connections = " << arrayToArrayConns.size() << endl;
  vector<vector<Connection> > cLists;
    
  return false;
}
