#include "coreir.h"
#include "coreir/passes/transform/packconnections.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::PackConnections::ID = "packconnections";
bool Passes::PackConnections::runOnModule(Module* m) {
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
                return cast<Select>(l.second)->getParent() <
                  cast<Select>(r.second)->getParent();
              });
  
  stable_sort(begin(arrayToArrayConns),
              end(arrayToArrayConns),
              [](const Connection& l,
                 const Connection& r) {
                return cast<Select>(l.first)->getParent() <
                  cast<Select>(r.first)->getParent();
              });

  if (arrayToArrayConns.size() == 0) {
    return false;
  }


  vector<vector<Connection> > packs;
  split_by(arrayToArrayConns,
           packs,
           [](const Connection& l, const Connection& r) {
             Select* lastL = cast<Select>(l.first);
             Select* lastR = cast<Select>(l.second);

             Select* nextL = cast<Select>(r.first);
             Select* nextR = cast<Select>(r.second);

             if (lastL->getParent() != nextL->getParent()) {
               return false;
             }

             if (lastR->getParent() != nextR->getParent()) {
               return false;
             }

             if ((stoi(lastL->getSelStr()) + 1) ==
                 stoi(nextL->getSelStr())) {

               if ((stoi(lastR->getSelStr()) + 1) ==
                   stoi(nextR->getSelStr())) {
                 return true;
               }                    
             }
                
             return false;
           });

  delete_if(packs, [](const vector<Connection>& conns) {
      assert(conns.size() > 0);

      auto conn = conns[0];
      Select* sel = cast<Select>(conn.first);
      ArrayType* tp = cast<ArrayType>(sel->getParent()->getType());

      return tp->getLen() != conns.size();
    });

  cout << "# of connections before deleting = " << def->getConnections().size() << endl;
  for (auto& gp : packs) {
    assert(gp.size() > 0);

    //cout << "Deleting pack of size " << gp.size() << endl;
    auto conn = gp[0];
    Select* selL = cast<Select>(conn.first);
    Select* selR = cast<Select>(conn.second);

    Wireable* parentL = selL->getParent();
    Wireable* parentR = selR->getParent();

    for (auto& conn : gp) {
      def->disconnect(conn.first, conn.second);
    }

    def->connect(parentL, parentR);
    
  }

  cout << "# of connections after deleting = " << def->getConnections().size() << endl;
  // cout << "GROUPS" << endl;
  // for (auto& gp : groups) {
  //   cout << "-------- Group" << endl;
  //   for (auto& conn : gp) {
  //     cout << "( " << conn.first->toString() << ", " << conn.second->toString() << " )" << endl;
  //   }
  // }

  // vector<Connection> connGroup;
  // connGroup.push_back(arrayToArrayConns[0]);
  // Select* lastLeft = cast<Select>(arrayToArrayConns[0].first);
  // Select* lastRight = cast<Select>(arrayToArrayConns[0].second);
  
  // for (uint i = 1; i < arrayToArrayConns.size(); i++) {

  //   Connection conn = arrayToArrayConns[i];

  //   Select* curLeft = cast<Select>(conn.first);
  //   Select* curRight = cast<Select>(conn.second);

  //   Wireable* curLeftParent = curLeft->getParent();
  //   Wireable* curRightParent = curRight->getParent();

  //   if ((curLeft->getParent() == lastLeft->getParent()) &&
  //       (curRight->getParent() == lastRight->getParent())) {
      
  //   } else {
  //     if (connGroup.size() > 0) {
  //       groups.push_back(connGroup);
  //     }

  //     connGroup = {};
  //   }
    
  //   lastLeft = curLeft;
  //   lastRight = curRight;

  // }

  // if (connGroup.size() > 0) {
  //   groups.push_back(connGroup);
  // }

  // cout << "--- Sorted connections" << endl;
  // for (auto& conn : arrayToArrayConns) {
  //   cout << "( " << conn.first->toString() << ", " << conn.second->toString() << " )" << endl;
  // }

  // Idea: Sort each pair so that the wireable with the lower value parent is
  // always on the lhs

  // Next: Sort the list of connections by lhs, then sort by rhs
  // 

  
  // cout << "# of array - array connections = " << arrayToArrayConns.size() << endl;
  // vector<vector<Connection> > cLists;
    
  return true;
}
