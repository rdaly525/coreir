#include "coreir/passes/transform/cse.h"

using namespace std;
using namespace CoreIR;

// Desired CoreIR iterators/functional methods
// breadth-first tree iterator on wireables
// depth-first tree iterator on wireables
// leaf-iterator on wireables (Only single bits)
// breadth-first iteration on types
// depth-first iterator on types
// leaf iterator on types 
// 'All' operator with a predicate
// 'Any' operator with a predicate
// 'Map' operator
// 'Filter' operator (both a modify and a return new)


//Some possible (untested) implementations of some of the functions
template <typename Cont, typename Pred>
Cont filterOver(const Cont &cont, Pred predicate) {
  Cont result;
  std::copy_if(cont.begin(), cont.end(), std::back_inserter(result), predicate);
  return result
}

template <typename InCont, typename OutCont, typename Fun>
OutCont mapOver(const InCont &cont, Fun fun) {
  OutCont result;
  std::transform(cont.begin(), cont.end(), std::back_inserter(result), fun);
  return result
}

template <typename Cont, typename Pred>
bool anyOf(const Cont &cont, Pred predicate) {
  return std::any_of(cont.begin(), cont.end(), predicate);
}

template <typename Cont, typename Pred>
bool allOf(const Cont &cont, Pred predicate) {
  return std::all_of(cont.begin(), cont.end(), predicate);
}


//This is a pass that will do generalized common subexpression elimination.
//a 'cse' is any time there are two instances of the same module which 
//are driven by identical values.
namespace CoreIR {

  namespace Passes {

    string Passes::CSE::ID = "cse";
    bool CSE::runOnModule(Module* m) {
      if (!m->hasDef()) {
        return false;
      }

      //create map from instance kind to list of instances
      std::map<Module*, std::vector<Instance*>> modules2Instances;
      for (auto ipair: m->getInstances()) {
        auto imod = instance->getModule();
        if (modules2Instances.count(imod)) {
          modules2Instances[imod] = {};
        }
        modules2Instances[imod].add(instance)
      }
      
      bool modified = false;
      for (auto mpair : modules2Instances) {
        auto mod = mpair.first;
        auto ilist = mpair.second;

        //instance list needs to have at least 2 instances
        if (ilist.size() < 2) {
          continue;
        }
        
        //Module cannot contain an inout port
        auto it = leaf_iter(mod->getType());
        bool has_inout = std::any_of(it.begin(), it.end(), [](Type* t) {
          return t->isInOut();
        });
        if (has_inout) {
          continue;
        }

        //Filter out any instances that have a connected mixed direction
        ilist = filterOver(ilist, [](Instance* inst) {
          auto iter = bfirst_iterator(inst);
          bool has_mixed = std::any_of(iter.begin(), iter.end(), [](Wireable* w) {
            return w->getConnectedWireables().size() > 0 &&
              w->getType()->isMixed();
          });
        });

        //Search for potential matches among the instance list
        //pop first from list
        //if has matches, add to matchlist
        //  pop all matches from list as well
        //This can be a helper function
        auto getInputsAndDirivers = [](Instance* inst) {
          auto iter = bfirst_iterator(inst);
          auto inputs = filterOver(iter.begin(), iter.end(), [](Wireable* w) {
            return w->getType()->isInput()
                && w->getConnectedPorts().size() > 0;
          });
          auto drivers = mapOver(cur_inputs, [](Wireable* w) {
            return w->getConnectedWireables()[0];
          }
          return zip(inputs, drivers);
        }
        //Queue to hold all the successful matches
        std::vector<std::vector<Instance*>> matchList;
        while (ilist.size() > 0) {
          Instance* cur = ilist.pop_back();
          auto curID = getInputsAndDrivers(cur)
          //matches need to have the same cur_inputs and cur_drivers
          auto matches = filterOver(ilist, [](Instance* inst) {
            auto instID = getInputsAndDrivers(inst)
            bool match = allOf(zip(curID, instID), [](auto p) {
              return p.first.first == p.second.first    //inputs are thes same
                  && p.second.first == p.second.second; //drivers are the same
            });
            return match;
          });

          //No matches, so continue
          if (matches.size() ==0) {
            continue;
          }
          modified = true;
          
          matches.push_back(cur);
          //matches now contains a list of instances all driven by identical wires
          matchList.push_back(matches);
          
          //remove matches from ilist
          std::remove_if(ilist.begin(), ilist.end(), [](Instance* inst) {
            return anyOf(matches, [](Instance* minst) {
              return inst == minst;
            });
          });
        }
        
        //matchList now contains a list of matches. Now to remove the duplicate instances
        for (auto matches : matchList) {
          assert(matches.size() > 1);
          //This one will be kept
          auto inst = matches.pop_back();
          auto iname = inst->getInstanceName();
          for (auto other : matches) {
            //find connected outputs
            auto it = bfirst_iter(other);
            auto outputs = filterOver(it.begin(), it.end(), [](Wireable* w) {
              return w->getType()->isOutput()
                  && w->getConnectedPorts().size() > 0;
            });
            for (auto output : outputs) {
              auto srcSP = output->getSelectPath();
              srcSP[0] = iname;
              for (dst : output->getConnectedPorts()) {
                auto dstSP = dst->getSelectPath();
                mod->addConnection(srcSP, dstSP);
              }
            }
            //Delete other instance (will also delete all connections)
            mod->removeInstance(other);
          });
        }
      }
      return modified;
    } //runOnModule
  } //Passes namespace
}//CoreIR namespace
