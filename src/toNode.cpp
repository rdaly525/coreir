#include "toNode.hpp"
#include <set>
#include <cassert>

/*
void emitConnections(FILE *out, bool firstIface, string firstString, Type* first,
                                bool secondIface, string secondString) {
  if (first->isType(INT)) {
    // can't connect two interface ports
    assert(!(firstIface && secondIface));
    if (firstIface) {
      fprintf(out, "    self.%s = %s\n", firstString.c_str(), secondString.c_str());
    } else if (secondIface) {
      fprintf(out, "    self.%s = %s\n", secondString.c_str(), firstString.c_str());
    } else {
      // one of them must be IN and the other must be OUT
      if (dynamic_cast<IntType*>(first)->getDir() == IN) {
        fprintf(out, "    %s.addInput(%s)\n", firstString.c_str(), secondString.c_str());
      } else {
        fprintf(out, "    %s.addInput(%s)\n", secondString.c_str(), firstString.c_str());
      }
    }
  } else if (first->isType(ARRAY)) {
    ArrayType* a = dynamic_cast<ArrayType*>(first);
    for (int i = 0; i < a->getLen(); i++) {
      emitConnections(out, firstIface, firstString + "_" + to_string(i), a->getBaseType(),
                           secondIface, secondString + "_" + to_string(i));
    }
  } else { // RECORD
    RecordType* r = dynamic_cast<RecordType*>(first);
    map<string,Type*> m = r->getRecord();
    for (map<string,Type*>::iterator it = m.begin(); it != m.end(); it++) { 
      emitConnections(out, firstIface, firstString + "_" + it->first, it->second,
                           secondIface, secondString + "_" + it->first);
    }
  }
}
*/

pair<WireableEnum, string> traceSelector(Wireable* selector) {
  pair<WireableEnum, string> result;
  while (selector->getBundleType() == SEL) {
    Select* sel = dynamic_cast<Select*>(selector);
    if (result.second.empty()) {
      result.second = sel->getSelStr();
    } else {
      result.second = sel->getSelStr() + "_" + result.second;
    }
    selector = sel->getParent();
  }
  if (selector->getBundleType() == INST) {
    result.second = dynamic_cast<Instance*>(selector)->getName() + "." + result.second;
  } else {
    result.second = "self." + result.second;
  }
  result.first = selector->getBundleType();
  return result;
}

void generateRefsForTypeHelper(Type* t, string curRef, vector<pair<Dir, string> >& refs) {
  string prefix = curRef.empty() ? curRef : curRef + "_";
  if (t->isType(INT)) {
    refs.push_back(make_pair(dynamic_cast<IntType*>(t)->getDir(), prefix + "i"));
  } else if (t->isType(ARRAY)) {
    ArrayType* at = dynamic_cast<ArrayType*>(t);
    for (int i = 0; i < at->getLen(); i++) {
      generateRefsForTypeHelper(at->getBaseType(), prefix + to_string(i), refs);
    }
  } else { // RECORD
    RecordType* rt = dynamic_cast<RecordType*>(t);
    map<string,Type*> m = rt->getRecord();
    for (map<string,Type*>::iterator it = m.begin(); it != m.end(); it++) { 
      generateRefsForTypeHelper(it->second, prefix + it->first, refs);
    }
  }
}

vector<pair<Dir, string> > generateRefsForType(Type *t) {
  vector<pair<Dir, string> > result;
  generateRefsForTypeHelper(t, "", result);
  return result;
}

string processConnectionPrefix(string trace) {
  return trace.back() == '.' ? trace : trace + "_";
}

void processConnection(FILE *out, Wireable* first, Wireable *second) {
  pair<WireableEnum, string> firstTrace = traceSelector(first);
  pair<WireableEnum, string> secondTrace = traceSelector(second);
  assert(!(firstTrace.first == IFACE && secondTrace.first == IFACE));
  
  vector<pair<Dir, string> > refs = generateRefsForType(first->getType());
  string firstPrefix = processConnectionPrefix(firstTrace.second);
  string secondPrefix = processConnectionPrefix(secondTrace.second);
  for (vector<pair<Dir, string> >::iterator it = refs.begin(); it != refs.end(); it++) {
    string firstWire = firstPrefix + it->second;
    string secondWire = secondPrefix + it->second;
    if (firstTrace.first == IFACE) {
      fprintf(out, "    %s = %s\n", firstWire.c_str(), secondWire.c_str());
    } else if (secondTrace.first == IFACE) {
      fprintf(out, "    %s = %s\n", secondWire.c_str(), firstWire.c_str());
    } else {
      if (it->first == IN) {
        fprintf(out, "    %s.addInput(%s)\n", firstWire.c_str(), secondWire.c_str());
      } else {
        fprintf(out, "    %s.addInput(%s)\n", secondWire.c_str(), firstWire.c_str());
      }
    }
  }
}

void toNode(FILE *out, Circuit* c, set<string>& processed) {
  if (processed.find(c->getName()) != processed.end()) {
    return;
  }

  if (!c->isPrimitive()) {
    Module* m = dynamic_cast<Module*>(c);
    vector<Instance*> instances = m->getInstances();
    for (vector<Instance*>::iterator it = instances.begin(); it != instances.end(); it++) {
      toNode(out, (*it)->getCircuitType(), processed);
    }
    // TODO add uniquifier to the name?
    fprintf(out, "\nclass %s:\n", c->getName().c_str());
    fprintf(out, "  def __init__(self):\n");
    for (vector<Instance*>::iterator it = instances.begin(); it != instances.end(); it++) {
      fprintf(out, "    %s = %s()\n", (*it)->getName().c_str(), (*it)->getCircuitType()->getName().c_str());
    }
    vector<Connection> connections = m->getConnections();
    for (vector<Connection>::iterator it = connections.begin(); it != connections.end(); it++) {
      processConnection(out, it->first, it->second);
    }
  } else {
    assert(c->getType()->isType(RECORD));
    RecordType* r = dynamic_cast<RecordType*>(c->getType());
    map<string,Type*> m = r->getRecord();
    // TODO add uniquifier to the name?
    fprintf(out, "\nclass %s:\n", c->getName().c_str());
    fprintf(out, "  def __init__(self):\n");
    fprintf(out, "    base = pnr.Node()\n");
    int numOuts = 0;
    for (map<string,Type*>::iterator it = m.begin(); it != m.end(); it++) { 
      // primitives should be smallest unit of composition; used composed
      // modules whenever possible
      assert(it->second->isType(INT));
      if (!it->second->hasInput()) {
        numOuts++;
      }
      fprintf(out, "    self.%s_i = base\n", it->first.c_str());
    }
    assert(numOuts == 1);
  }

  processed.insert(c->getName());
}


void toNodeMain(Circuit* c) {
  FILE* out = fopen("circuit.py", "w");
  set<string> processed;
  fprintf(out, "import doit\n");
  fprintf(out, "import pnr\n");
  toNode(out, c, processed);
  fprintf(out, "\ndef run():\n");
  vector<pair<Dir, string> > refs = generateRefsForType(c->getType());
  fprintf(out, "  top = %s()\n", c->getName().c_str());
  fprintf(out, "  nodes = []\n");
  fprintf(out, "  for n in [");
  for (vector<pair<Dir, string> >::iterator it = refs.begin(); it != refs.end(); it++) {
    if (it->first == IN) {
      fprintf(out, "top.%s, ", it->second.c_str());
    }
  }
  fprintf(out, "]:\n");
  fprintf(out, "    nodes += n.flatten()\n"); 
  fprintf(out, "  doit.doit(nodes)\n");
  fprintf(out, "\nif __name__ == \"__main__\":\n");
  fprintf(out, "  run()");
  fclose(out);
}
