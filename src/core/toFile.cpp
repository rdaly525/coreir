#include "toFile.hpp"
#include <set>
#include <cassert>

string traceSelector(Wireable* selector) {
  string result;
  while (selector->isKind(SEL) || selector->isKind(TSEL)) {
    Select* sel = dynamic_cast<Select*>(selector);
    if (result.empty()) {
      result = sel->getSelStr();
    } else {
      result = sel->getSelStr() + "." + result;
    }
    selector = sel->getParent();
  }
  if (selector->isKind(INST) || selector->isKind(TINST)) {
    result = dynamic_cast<Instance*>(selector)->getInstname() + "." + result;
  } else {
    result = "this." + result;
  }
  return result;
}

void emitTypeJSON(FILE *out, Type *t) {
  if (t->isKind(INT)) { 
    fprintf(out, "{\"type\": \"int\"}");
  } else if (t->isKind(ARRAY)) {
    ArrayType* at = dynamic_cast<ArrayType*>(t);
    fprintf(out, "{\"type\": \"array\", \"width\": %d, \"element\": ", at->getLen());
    emitTypeJSON(out, at->getElemType());
    fprintf(out, " }");
  } else if (t->isKind(RECORD)) {
    RecordType* rt = dynamic_cast<RecordType*>(t);
    fprintf(out, "{\"type\": \"record\", \"fields\": {");
    map<string, Type*> record = rt->getRecord();
    vector<string> order = rt->getOrder(); 
    for (vector<string>::iterator it = order.begin(); it != order.end(); it++) {
      fprintf(out, "\"%s\": ", (*it).c_str()); 
      emitTypeJSON(out, record.find(*it)->second);
      fprintf(out, ", ");
    }
    fprintf(out, "}}");
  }
}

void processConnection(FILE *out, Wireable* first, Wireable *second) {
  string firstTrace = traceSelector(first);
  string secondTrace = traceSelector(second);
  fprintf(out, "{\"first\": \"%s\", \"second\": \"%s\"},\n", firstTrace.c_str(), secondTrace.c_str());  
}

void toFile(FILE *out, Instantiable* c, set<string>& processed) {
  if (processed.find(c->getQualifiedName()) != processed.end()) {
    return;
  }

  if (c->isKind(MDEF) || c->isKind(TMDEF)) {
    ModuleDef* m = dynamic_cast<ModuleDef*>(c);
    vector<Instance*> instances = m->getInstances();
    for (vector<Instance*>::iterator it = instances.begin(); it != instances.end(); it++) {
      toFile(out, (*it)->getInstRef(), processed);
      GenArgs *genArgs = (*it)->getGenArgs();
      if (genArgs != nullptr) {
        vector<GenArg*> args = genArgs->args;
	for (vector<GenArg*>::iterator ga = args.begin(); ga != args.end(); ga++) {
	  if ((*ga)->kind == GMOD) { 
	    toFile(out, dynamic_cast<GenMod*>(*ga)->mod, processed);
          }
	}
      }
    }
    // TODO add uniquifier to the name?
    fprintf(out, "{\"kind\": \"mdef\", \"name\": \"%s\",\n\"type\": ", c->getQualifiedName().c_str());
    emitTypeJSON(out, m->getType());
    fprintf(out, ",\n\"modules\": [\n");
    for (vector<Instance*>::iterator it = instances.begin(); it != instances.end(); it++) {
      Instantiable *inst = (*it)->getInstRef();
      fprintf(out, "{\"name\": \"%s\"", (inst->getQualifiedName() + " " + (*it)->getInstname()).c_str());
      if ((*it)->getGenArgs() != nullptr) {
	fprintf(out, ", \"genargs\": [");
	vector<GenArg*> args = (*it)->getGenArgs()->args;
	for (vector<GenArg*>::iterator ga = args.begin(); ga != args.end(); ga++) {
	  GenArg *arg = *ga;
	  if (arg->kind == GSTRING) {
	    fprintf(out, "{\"type\": \"string\", \"data\": \"%s\"}, ", dynamic_cast<GenString*>(arg)->str.c_str());
          } else if (arg->kind == GINT) {
	    fprintf(out, "{\"type\": \"int\", \"data\": %d}, ", dynamic_cast<GenInt*>(arg)->i);
	  } else if (arg->kind == GMOD) {
	    fprintf(out, "{\"type\": \"module\", \"data\": \"%s\"}, ", dynamic_cast<GenMod*>(arg)->mod->getQualifiedName().c_str());
	  }
	}
	fprintf(out, "]");
      }
      fprintf(out, "},\n");
    }
    fprintf(out, "],\n\"connections\": [\n");
    vector<Wiring> connections = m->getWirings();
    for (vector<Wiring>::iterator it = connections.begin(); it != connections.end(); it++) {
      processConnection(out, it->first, it->second);
    }
    fprintf(out, "]\n},\n");
  } else if (c->isKind(MDEC)) {
    fprintf(out, "{\"kind\": \"mdec\", \"name\": \"%s\"},\n", c->getQualifiedName().c_str());
  } else if (c->isKind(GDEC)) {
    fprintf(out, "{\"kind\": \"gdec\", \"name\": \"%s\"},\n", c->getQualifiedName().c_str());
  } else {
    // TODO unclear what to do here (GDEF)
  }

  processed.insert(c->getQualifiedName());
}

void toFileMain(Instantiable* c, string filename) {
  FILE* out = fopen(filename.c_str(), "w");
  fprintf(out, "{\n\"modules\": [\n");
  set<string> processed;
  toFile(out, c, processed);
  fprintf(out, "],\n\"main\": \"%s\"\n}", c->getQualifiedName().c_str());
  fclose(out);
}
