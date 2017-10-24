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

//TODO get rid of
using namespace std;

namespace CoreIR {
namespace Passes {

// <<<<<<< HEAD
//   class VWire {
//     std::string name;
//     unsigned dim;
//     Type::DirKind dir;
// =======
class VWire {
  std::string name;
  bool isArray;
  unsigned dim;
  Type::DirKind dir;
  //>>>>>>> upstream/dev
  public :
    VWire(std::string field,Type* t) : name(field), isArray(isa<ArrayType>(t)), dim(t->getSize()), dir(t->getDir()) {}
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
      if (!isArray) return "";
      return "["+std::to_string(dim-1)+":0]";
    }
    std::string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    std::string getName() { return name;}
  };


// <<<<<<< HEAD
//   class VModule {
//     std::string modname;
//     std::unordered_map<std::string,VWire> ports;
//     std::unordered_set<std::string> params;
//     std::unordered_map<std::string,std::string> paramDefaults;
// =======
class VModule {
  public :
    typedef std::set<std::string> SParams;
    typedef std::map<std::string,std::string> SMap;
  private:
  std::string modname;
  std::map<std::string,VWire> ports;
  std::vector<std::string> interface;
  SParams params;
  SMap paramDefaults;
  //>>>>>>> upstream/dev

    Generator* gen = nullptr;
  
    std::vector<std::string> stmts;
  public:
    
    VModule(std::string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    VModule(Module* m) : VModule(m->getName(),m->getType()) {
      if (m->generated()) this->modname = m->getLongName();
      this->addParams(params,m->getModParams());
      this->addDefaults(paramDefaults,m->getDefaultModArgs());
      this->checkJson(m->getMetaData());
    }
    VModule(Generator* g) : modname(g->getName()), gen(g) {
      this->addParams(params,g->getGenParams());
      this->addDefaults(paramDefaults,g->getDefaultGenArgs());
      this->checkJson(g->getMetaData());
    }
    void checkJson(json jmeta) {
      if (jmeta.count("verilog") ) {
        if (jmeta["verilog"].count("prefix")) {
          this->modname = jmeta["verilog"]["prefix"].get<std::string>() + this->modname;
        }
        if (jmeta["verilog"].count("definition")) {
          stmts.push_back(jmeta["verilog"]["definition"].get<std::string>());
        }
        if (jmeta["verilog"].count("interface")) {
          interface = (jmeta["verilog"]["interface"].get<std::vector<std::string>>());
        }
        if (jmeta["verilog"].count("parameters")) {
          for (auto p : jmeta["verilog"]["parameters"].get<std::vector<std::string>>()) {
            this->params.insert(p);
          }
        }
      }
// <<<<<<< HEAD

//       this->addParams(g->getGenParams());
//       this->addDefaults(g->getDefaultGenArgs());
//     }

// =======
    }
    std::string getName() { return modname;}
    bool hasDef() {return stmts.size() > 0 && (interface.size()>0 || ports.size()>0);}
  //>>>>>>> upstream/dev
    void addStmt(std::string stmt) { stmts.push_back(stmt); }

    std::string toCommentString() {
      return "//Module: " + modname + " defined externally";
    }

    std::string toString();

    std::string toInstanceString(Instance* inst);

  private :
// <<<<<<< HEAD

//     void Type2Ports(Type* t,std::unordered_map<std::string,VWire>& ports) {
// =======
    void Type2Ports(Type* t,std::map<std::string,VWire>& ports) {
      //>>>>>>> upstream/dev
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
	ports.emplace(rmap.first,VWire(rmap.first,rmap.second));
      }
    }
// <<<<<<< HEAD

//     void addParams(Params ps) {

//       for (auto p : ps) {
// 	if (params.count(p.first) != 0) {

// 	  ASSERT(params.count(p.first)==0,"NYI Cannot have duplicate params");
// 	}
// 	params.insert(p.first); 
//       }
//     }

//     void addDefaults(Values ds) { 
//       for (auto dpair : ds) {
// 	ASSERT(params.count(dpair.first),"NYI Cannot Add default!");
// 	paramDefaults[dpair.first] = dpair.second->toString();
// =======
    std::string p2Str(std::set<std::string> ss) {
      return "(" + join(ss.begin(),ss.end(),string(",")) + ")";
    }
    void addParams(SParams& sps, Params ps) { 
      for (auto p : ps) {
        ASSERT(sps.count(p.first)==0,"NYI Cannot have duplicate params\n"+ this->p2Str(sps) + " already has " + p.first);
        sps.insert(p.first); 
      }
    }
    void addDefaults(SMap sm, Values ds) { 
      for (auto dpair : ds) {
        ASSERT(params.count(dpair.first),modname + " NYI Cannot Add default! " + dpair.first);
        sm[dpair.first] = toConstString(dpair.second);
      }
    }
    std::string toConstString(Value* v) {
      if (auto av = dyn_cast<Arg>(v)) {
        return av->getField();
      }
      else if (auto iv = dyn_cast<ConstInt>(v)) {
        return iv->toString();
      }
      else if (auto bv = dyn_cast<ConstBool>(v)) {
        return std::to_string(uint(bv->get()));
      }
      else if (auto bvv = dyn_cast<ConstBitVector>(v)) {
        BitVector bv = bvv->get();
        return std::to_string(bv.bitLength())+"'d"+std::to_string(bv.to_type<uint64_t>());
	//>>>>>>> upstream/dev
      }
      //TODO could add string
      assert(0);
    }

// <<<<<<< HEAD
//   };
// =======

};
  //>>>>>>> upstream/dev


}
}

#endif
