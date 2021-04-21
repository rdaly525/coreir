#ifndef COREIR_PASSMANAGER_HPP_
#define COREIR_PASSMANAGER_HPP_

#include <memory>
#include <stack>
#include "fwd_declare.h"
#include "symbol_table_interface.hpp"

namespace CoreIR {

class InstanceGraph;

class PassManager {
  Context* c;
  std::vector<Namespace*> nss;

  // Data structure for storing passes
  std::map<std::string, Pass*> passMap;

  // Name to isValid
  std::map<std::string, bool> analysisPasses;

  std::vector<std::string> passLog;

  bool debug = false;

 public:
  explicit PassManager(Context* c);
  ~PassManager();
  Context* getContext() { return c; }

  void addPass(Pass* p);

  // Runs all passes in order over namespaces
  // Returns if graph was modified
  bool run(
    std::vector<std::string>& passes,
    std::vector<std::string> namespaceName = {"global"});
  bool isAnalysisCached(std::string);
  void printLog();
  void printPassChoices();

  Pass* getAnalysisPass(std::string ID) {
    assert(passMap.count(ID));
    return passMap[ID];
  }

  SymbolTableInterface* getSymbolTable() { return symbolTable.get(); }

 private:
  void pushAllDependencies(std::string oname, std::stack<std::string>& work);

  friend class Pass;
  bool runPass(Pass* p, std::vector<std::string>&);

  bool runContextPass(Pass* p);
  bool runNamespacePass(Pass* p);
  bool runModulePass(Pass* p);
  bool runInstancePass(Pass* p);
  bool runInstanceVisitorPass(Pass* p);
  bool runInstanceGraphPass(Pass* p);

  std::unique_ptr<SymbolTableInterface> symbolTable;
};

}  // namespace CoreIR
#endif  // PASSMANAGER_HPP_
