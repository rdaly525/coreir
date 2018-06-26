#ifndef COREIR_FIRRTL_HPP_
#define COREIR_FIRRTL_HPP_

#include "coreir.h"
#include <ostream>

namespace CoreIR {
namespace Passes {

using namespace std;
class FModule {
  Context* c;
  std::string name;
  std::vector<std::string> io;
  std::map<std::string,std::string> gparams;
  std::vector<std::string> params;
  std::vector<std::string> stmts;
  public : 
    FModule(Module* m) : c(m->getContext()), name(m->getLongName()) {
      addModuleIOs(cast<RecordType>(m->getType()));
      for (auto ppair : m->getModParams()) {
        auto vtype = ppair.second;
        uint n;
        if (isa<BoolType>(vtype)) n = 1;
        else if (auto bv = dyn_cast<BitVectorType>(vtype)) {
          n = bv->getWidth();
        }
        else ASSERT(0,"NYI");
        io.push_back("input " + ppair.first + " : UInt<" + std::to_string(n) + ">");
      }
      if (m->isGenerated()) {
        checkJson(m->getGenerator()->getMetaData(),m->getGenArgs());
      }
      checkJson(m->getMetaData(),Values()); //TODO deal with linking
    }
    std::string getName() { return name;}
    void checkJson(json jmeta,Values genargs) {
      if (jmeta.count("firrtl") ) {
        if (jmeta["firrtl"].count("prefix")) {
          this->name = jmeta["firrtl"]["prefix"].get<std::string>() + this->name;
        }
        if (jmeta["firrtl"].count("definition")) {
          for (auto stmt : jmeta["firrtl"]["definition"].get<std::vector<std::string>>()) {
            addStmt(stmt);
          }
        }
        if (jmeta["firrtl"].count("parameters")) {
          auto gp = (jmeta["firrtl"]["parameters"].get<std::vector<std::string>>());
          for (auto p : gp) {
            ASSERT(genargs.count(p),"Missing param" + p);
            if (p=="hi") { //Sketch annoying hack. Need to subtract 1 for indicies
              this->gparams["%"+p+"%"] = std::to_string(genargs[p]->get<int>()-1);
            }
            else {
              this->gparams["%"+p+"%"] = genargs[p]->toString();
            }
          }
        }
      }
    }
    bool hasDef() {return stmts.size()>0;}
    void addStmt(std::string stmt) {
      stmts.push_back(stmt);
    }

    // Add statements for the given IO record.
    void addModuleIOs(RecordType* rt) {
      for (auto rpair : rt->getRecord()) {
        std::string io_name = rpair.first;
        Type* t = rpair.second;
        auto io_type = std::string(t->isInput() ? "input" : "output");

        // Assumes mixed types are outputs...
        addStmt(io_type + " " + io_name + " : " + type2firrtl(t, t->isInput()));

        // For output types that are UInt, add wires for each sub-bit since
        // CoreIR supports subword assignment and FIRRTL does not.
        if (!t->isInput() && !(getUIntWidth(t) < 0)) {
          int width = getUIntWidth(t);
          for (int i = 0; i < width; i++) {
            addStmt("wire " + getOutputBitWire(io_name, i) + " : UInt<1>");
          }

          // Now wire up the bit wires to the main output wire.
          std::string cat_node;
          if (width < 2) {
            // No need for cat if the width is 1.
            cat_node = getOutputBitWire(io_name, 0);
          } else {
            cat_node = "cat(" + getOutputBitWire(io_name, width - 1) + ", " + getOutputBitWire(io_name, width - 2) + ")";
            for (int i = width - 3; i >= 0; i--) {
              cat_node = "cat(" + cat_node + ", " + getOutputBitWire(io_name, i) + ")";
            }
          }
          addStmt(io_name + " <= " + cat_node);
        }
      }
    }

    // Get the wire name for the specified bit in the given output IO.
    static std::string getOutputBitWire(std::string name, int index) {
      // TODO: check/verify that there isn't a conflicting wire in the design...
      return name + "_b" + std::to_string(index);
    }

    std::string type2firrtl(Type* t, bool isInput);

    // Return the width of the given type if it is a UInt, or -1 if it is not a
    // UInt.
    int getUIntWidth(Type* t);

    std::string toString();
};



class Firrtl : public InstanceGraphPass {
  std::map<Module*,FModule*> modMap;
  std::vector<FModule*> fmods;
  public :
    static std::string ID;
    Firrtl() : InstanceGraphPass(ID,"Creates Firrtl representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity-onlyinputs"); //Should change back to check all connections
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
