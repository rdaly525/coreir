#include "coreir.h"
#include "coreir/passes/transform/add_dummy_inputs.h"

using namespace std;
using namespace CoreIR;

string Passes::AddDummyInputs::ID = "add-dummy-inputs";

bool Passes::AddDummyInputs::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  auto def = m->getDef();
  auto c = def->getContext();

  bool addedDummy = false;

  auto instances = def->getInstances();
  set<Instance*> toCheck;
  for (auto instR : instances) {
    toCheck.insert(instR.second);
  }

  //cout << "Running on module " << m->toString() << endl;

  while (toCheck.size() > 0) {
    Instance* next = *begin(toCheck);
    Module* mr = next->getModuleRef();
    RecordType* tp = mr->getType();
    //cout << "\tChecking instance " << next->toString() << endl;
    for (auto field : tp->getFields()) {
      Select* sel = next->sel(field);

      if (sel->getType()->getDir() == Type::DirKind::DK_In) {

        if (getSourceSelects(sel).size() == 0) {
          //cout << "\t\t" << sel->toString() << endl;
          //assert(isBitArray(*(sel->getType())) || isBitType(*(sel->getType())));

          if (isBitArray(*(sel->getType()))) {
            ArrayType* arrTp = cast<ArrayType>(sel->getType());
            int width = arrTp->getLen();
            string constName = next->toString() + "_" + field + "_const_in";
            auto replaceConst =
              def->addInstance(constName,
                               "coreir.const",
                               {{"width", Const::make(c, width)}},
                               {{"value", Const::make(c, BitVector(width, 0))}});

            def->connect(replaceConst->sel("out"), sel);
          } else {
            assert(isBitType(*(sel->getType())));

            string constName = next->toString() + "_" + field + "_const_in";
            auto replaceConst =
              def->addInstance(constName,
                               "corebit.const",
                               {{"value", Const::make(c, false)}});

            def->connect(replaceConst->sel("out"), sel);
            
          }
          
        }
        
      }
    }

    toCheck.erase(next);
  }
  
  return addedDummy;
}

// {top}.pe_0xF.in_BUS1_S3_T4 Is not connected
