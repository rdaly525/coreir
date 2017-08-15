
#include "coreir.h"
#include "coreir-passes/flattenconnections.hpp"
#include "queue"

bool checkValidType(Type* t) {
  if (isa<BitType>(t) || isa<BitInType>(t)) return true;
  if (auto at = dyn_cast<ArrayType>(t)) {
    Type* elemType = at->getElemType();
    return isa<BitType>(elemType) || isa<BitInType>(elemType);
  }
  return false;
}

vector<string> getAllPossibleSelects(Type* t) {
  vector<string> sels;
  if (auto at = dyn_cast<ArrayType>(t)) {
    for (uint i=0; i<at->getLen(); ++i) {
      sels.push_back(to_string(i));
    }
  }
  else if (auto rt = dyn_cast<RecordType>(t)) {
    for (auto r : rt->getRecord()) {
      sels.push_back(r.first);
    }
  }
  return sels;
}


bool FlattenConnections::runOnModule(Module* m) {
  if (!m->hasDef()) return false;
  bool changed = false;
  //Load up a queue of connections
  ModuleDef* def = m->getDef();
  queue<Connection> cons;
  for (auto con : def->getConnections()) {
    cons.push(con);
  }
  while (!cons.empty()) {
    auto con = cons.front();
    cons.pop();
    if (checkValidType(con.first->getType())) {
      continue;
    }
    else {
      changed = true;
      def->disconnect(con.first,con.second);
      for (auto selstr : getAllPossibleSelects(con.first->getType())) {
        def->connect(con.first->sel(selstr),con.second->sel(selstr));
        assert(def->hasConnection(con.first->sel(selstr),con.second->sel(selstr)));
        cons.push(def->getConnection(con.first->sel(selstr),con.second->sel(selstr)));
      }
    }
  }
  return changed;
}

void FlattenConnections::print() {
  cout << "Ran flatten connections" << endl;

}
