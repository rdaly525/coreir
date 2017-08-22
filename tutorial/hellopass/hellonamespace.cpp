
/*
 * We are going to start by writing a simple namespace pass.
 * Namespaces are similar to an LLVM Module. They contain
 * Modules, Generators, TypeGens and NamedTypes. 
 * 
 * A Namespace Pass is the most general pass. It can analysize 
 * or transfrom the IR in any way it wants.
 */

#include "coreir.h"
using namespace CoreIR;

//Start by inheriting from one of the premade Pass Types
//  NamespacePass, ModulePass, InstancePass
class HelloNamespace : public NamespacePass {
  public :
    //Declare a std::static string called ID. This is necessary
    //in order for the PassManager to uniquely identify the pass.
    static std::string ID;
    
    //the Pass Constructor looks like:
    //  NamespacePass(std::string ID, std::string description, bool isAnalysis=false)
    HelloNamespace() : NamespacePass(ID,"External Hello namespace Pass") {}

    //This function is where the magic happens. It will be called for each namespace
    //You as the pass writer will define this function
    bool runOnNamespace(Namespace* n) override;
};

//Give this pass a unique name. This is how we will reference it
string HelloNamespace::ID = "hellonamespace";
bool HelloNamespace::runOnNamespace(Namespace* ns) {
  cout << "Hello! I am running on Namespace: " << ns->getName() << endl;

  cout << ns->getName() << " contains the following Modules:" << endl;
  for (auto mmap : ns->getModules()) { 
    // Modules are stored in an unordered_map<string,Generator*>
    // Generators, NamedTypes, Namespaces, Instances, etc are also all unordered_maps
    string modulename = mmap.first;
    Module* m = mmap.second;
    
    cout << "  Module Name is: " << modulename << endl;
    cout << "    " << m->getName() << " is the same name!" << endl;
  }
  cout << endl;
  
  cout << ns->getName() << " contains the following Generators:" << endl;
  for (auto gmap : ns->getGenerators()) {
    //Generators are also stored in an unordered_map<string,Generator*>
    string generatorname = gmap.first;
    Generator* g = gmap.second;
    
    cout << "  Generator Name is: " << generatorname << endl;
    cout << "    " << g->getName() << " is also my name" << endl;
  }
  cout << endl;

  cout << "I could also just call the print function!" << endl;
  ns->print();

  //This return value indicates whether the function has modified the graph.
  //This is important so the PassManager can verify the IR and rerun any analysis passes
  return false;
}


//In order to link these passes in to the standalone coreir tool, you will need to write the following two functions: registerPass and deletePass.
extern "C" Pass* registerPass() {
  //Simply just return a new version of your Pass
  return new HelloNamespace;
}

extern "C" void deletePass(Pass* p) {
  delete p;
}
