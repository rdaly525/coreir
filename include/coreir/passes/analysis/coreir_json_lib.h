#pragma once

#include <map>
#include <set>
#include "coreir.h"

using namespace CoreIR;
namespace CoreIR {
namespace JsonLib {

inline std::string tab(uint s) {
  std::string ret = "";
  for (uint i = 0; i < s; ++i) { ret += " "; }
  return ret;
}
inline std::string quote(std::string s) { return "\"" + s + "\""; }

class Dict {
  std::string ts = "";
  std::vector<std::string> fields;
  std::map<std::string, std::string> sorted;

 public:
  Dict(uint i) : ts(tab(i)) {}
  Dict() {}
  bool isEmpty() { return fields.size() == 0; }
  void add(std::string field, std::string val) {
    fields.push_back(quote(field) + ":" + val);
    sorted[field] = quote(field) + ":" + val;
  }
  std::string toMultiString(bool sort = false) {
    if (sort) {
      fields.clear();
      for (auto fmap : sorted) { fields.push_back(fmap.second); }
    }
    return "{\n" + ts + "  " +
           join(fields.begin(), fields.end(), ",\n" + ts + "  ") + "\n" + ts + "}";
  }
  std::string toString() {
    return "{" + join(fields.begin(), fields.end(), std::string(", ")) + "}";
  }
};

class Array {
  std::string ts = "";
  std::vector<std::string> fields;

 public:
  Array(uint i) : ts(tab(i)) {}
  Array() {}
  void add(std::string field) { fields.push_back(field); }
  std::string toString() {
    return "[" + join(fields.begin(), fields.end(), std::string(",")) + "]";
  }
  std::string toMultiString() {
    return "[\n" + ts + "  " +
           join(fields.begin(), fields.end(), ",\n" + ts + "  ") + "\n" + ts + "]";
  }
};

//Can specify which modules are added
struct GeneratorJson {
  Generator* g;
  std::vector<std::string> modules;

  GeneratorJson(Generator* g) : g(g) {}
  void add_module(Module* m, bool onlyDecl);
  std::string serialize();
};

struct TypeGenJson {
  TypeGen* tg;
  std::map<std::string, std::string> types;

  TypeGenJson(TypeGen* tg) : tg(tg) {}
  void add_type(Values v, Type* t);
  std::string serialize();
};

struct NamespaceJson {
  Namespace* ns;
  std::map<std::string, GeneratorJson> generators;
  std::map<std::string, TypeGenJson> typegens;
  std::map<std::string, std::string> modules;

  NamespaceJson(Namespace* ns) : ns(ns) {}
  void add_module(Module* m, bool onlyDecl);
  TypeGenJson& getOrCreateTypeGen(TypeGen* tg);
  std::string serialize();
};

std::string ns2Json(Namespace* ns);

}  // jsonlib
}  // coreir

