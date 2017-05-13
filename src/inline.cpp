

#include "wireable.hpp"

//This will modify the moduledef to inline the instance
void inlineModule(Instance* inst) {
  
  ModuleDef* def = inst->getModuleDef();
  Module* mod = def->getModule();
  Module* modInline = inst->getModuleRef();
  if (!modInline->hasDef()) {
    cout << "Cannot inline a module with no definition!" << endl;
    return;
  }
  ModuleDef* defInline = modInline->getDef();
  string modInlineName = modInline->getName();

  //I will be inlining defInline into def

  //First add all the instances of defInline into def. And add them to a map
  for (auto instmap : defInline->getInstances()) {
    string iname = modInlineName + "&" + instmap.first;
    def->addInstance(instmap.second,iname);
  }
  
  //Now add all the connections
  for (auto cons : defInline->getConnections()) {
    SelectPath pA = cons.first->getSelectPath();
    SelectPath pB = cons.second->getSelectPath();
    
    //Easy case: when neither are connect to self
    if (pA[0] != "self" && pB[0] != "self") {
      //Create the correct names and connect
      pA[0] = modInlineName + "&" + pA[0];
      pB[0] = modInlineName + "&" + pB[0];
      def->connect(pA,pB);
    }
    else { //Case for all the boundry connections



    }
  }


}
