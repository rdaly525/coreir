#ifndef COREIR_VMODULE_HPP_
#define COREIR_VMODULE_HPP_


//What I need to represent
//
//Wire(std::string name, int bits)
//
//ModuleDec((Wire w,std::string dir)* puts,stmt* stmsts)
//Stmt = std::string
//     | WireDec(Wire w)
//     | Assigns(std::string left, std::string right)
//     | Instance(std::string modname,(Wire l, Wire r)*)
//
//Expr = std::string
//     | Wire


#include "coreir.h"

namespace CoreIR {
namespace Passes {

  class VWire {
    std::string name;
    unsigned dim;
    Type::DirKind dir;
  public :
    VWire(std::string field,Type* t) : name(field), dim(t->getSize()), dir(t->getDir()) {}
    VWire(Wireable* w) : VWire("",w->getType()) {
      SelectPath sp = w->getSelectPath();
      if (sp.size()==3) {
        ASSERT(dim==1 && !isNumber(sp[1]) && isNumber(sp[2]),"DEBUG ME:");
        name = sp[1]+"["+sp[2]+"]";
      }
      else if (sp.size()==2) {
        ASSERT(!isNumber(sp[1]),"DEBUG ME:");
        name = sp[1];
      }
      else {
        assert(0);
      }
      if (sp[0] != "self") {
        name = sp[0]+ "_" + name;
      }
    }
    VWire(std::string name, unsigned dim, Type::DirKind dir) : name(name), dim(dim), dir(dir) {}
    std::string dimstr() {
      if (dim==1) return "";
      return "["+std::to_string(dim-1)+":0]";
    }
    std::string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    std::string getName() { return name;}
  };


  class VModule {
    std::string modname;
    std::unordered_map<std::string,VWire> ports;
    std::unordered_set<std::string> params;
    std::unordered_map<std::string,std::string> paramDefaults;

    Generator* gen = nullptr;
  
    std::vector<std::string> stmts;
  public:
    VModule(std::string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    VModule(Module* m) : VModule(m->getName(),m->getType()) {
      const json& jmeta = m->getMetaData();
      if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
        modname = jmeta["verilog"]["prefix"].get<std::string>() + m->getName();
      }

      this->addParams(m->getModParams());
      this->addDefaults(m->getDefaultModArgs());
    }
    VModule(Generator* g) : modname(g->getName()), gen(g) {
      const json& jmeta = g->getMetaData();
      if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
        modname = jmeta["verilog"]["prefix"].get<std::string>() + g->getName();
      }

      this->addParams(g->getGenParams());
      this->addDefaults(g->getDefaultGenArgs());
    }

    void addStmt(std::string stmt) { stmts.push_back(stmt); }

    std::string toCommentString() {
      return "//Module: " + modname + " defined externally";
    }

    std::string toString();

    std::string toInstanceString(Instance* inst);

  private :

    void Type2Ports(Type* t,std::unordered_map<std::string,VWire>& ports) {
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
	ports.emplace(rmap.first,VWire(rmap.first,rmap.second));
      }
    }

    void addParams(Params ps) {

      for (auto p : ps) {
	if (params.count(p.first) != 0) {

	  ASSERT(params.count(p.first)==0,"NYI Cannot have duplicate params");
	}
	params.insert(p.first); 
      }
    }

    void addDefaults(Values ds) { 
      for (auto dpair : ds) {
	ASSERT(params.count(dpair.first),"NYI Cannot Add default!");
	paramDefaults[dpair.first] = dpair.second->toString();
      }
    }

  };

}
}

#endif
