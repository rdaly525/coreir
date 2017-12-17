#include "coreir/simulator/dag_optimization.h"

#include "coreir/simulator/layout.h"
#include "coreir/simulator/multithreading.h"

using namespace std;

namespace CoreIR {

  vector<SIMDGroup>
  groupIdenticalSubDAGs(const vector<SubDAG>& dags,
                        const NGraph& g,
                        const int groupSize,
                        LayoutPolicy& lp) {

    vector<SIMDGroup> groups;

    uint i;
    for (i = 0; i < dags.size(); i += groupSize) {
      if ((i + groupSize) > dags.size()) {
        break;
      }

      vector<SubDAG> sg;
      for (int j = 0; j < groupSize; j++) {
        sg.push_back(dags[i + j]);
      }
      groups.push_back({groupSize, sg});
    }

    if (i < dags.size()) {
      vector<SubDAG> sg;      
      for (; i < dags.size(); i++) {
        sg.push_back(dags[i]);
      }

      groups.push_back({groupSize, sg});
    }

    // Force adjacency
    vector<vector<string> > state_var_groups;
    for (uint i = 0; i < groups.size(); i++) {
      vector<SubDAG>& group = groups[i].nodes;

      auto dag = group[0];

      // Create forced variable groups in layout
      for (uint i = 0; i < dag.size(); i++) {
        vdisc vd = dag[i];

        if (isSubgraphInput(vd, dag, g)) {  
          vector<string> invars;
          for (auto& dag : group) {
            auto vd = dag[i];
            string stateInLoc =
              cVar(*(g.getNode(vd).getWire()));

            invars.push_back(stateInLoc);
            lp.outputVarName(*(g.getNode(vd).getWire()));
          }

          state_var_groups.push_back(invars);
        }

        if (isSubgraphOutput(vd, dag, g)) {
          vector<string> outvars;

          for (auto& dag : group) {
            auto vd = dag[i];
            string stateOutLoc =
              cVar(*(g.getNode(vd).getWire()));

            lp.outputVarName(*(g.getNode(vd).getWire()));

            outvars.push_back(stateOutLoc);
          }

          state_var_groups.push_back(outvars);
          
        }
      }

    }

    cout << "====== State var groups" << endl;
    for (auto& gp : state_var_groups) {
      cout << "--------- Group" << endl;
      for (auto& var : gp) {
        cout << "-- " << var << endl;
      }
    }

    for (auto& gp : state_var_groups) {
      lp.forceAdjacent(gp);
    }
    
    return groups;
  }

  CircuitPaths buildCircuitPaths(const std::deque<vdisc>& topoOrder,
                                 NGraph& g,
                                 Module& mod) {
    CircuitPaths paths;

    vector<set<vdisc>> ccs =
      connectedComponentsIgnoringInputs(g);

    cout << "# of connected components = " << ccs.size() << endl;

    // Group the graph components
    vector<SubDAG> seqToSeq;
    vector<SubDAG> seqToComb;
    vector<SubDAG> seqToMixed;

    vector<SubDAG> combToSeq;
    vector<SubDAG> combToComb;
    vector<SubDAG> combToMixed;
    
    vector<SubDAG> mixedToSeq;
    vector<SubDAG> mixedToComb;
    vector<SubDAG> mixedToMixed;
    

    // Set presequential DAGs
    for (auto& cc : ccs) {
      deque<vdisc> nodes;

      for (auto& vd : topoOrder) {
        if (elem(vd, cc)) {
          nodes.push_back(vd);
        }
      }

      if (subgraphHasCombinationalOutput(nodes, g) &&
          subgraphHasSequentialOutput(nodes, g) &&
          subgraphHasCombinationalInput(nodes, g)) {
        // Need to split up graphs of this form
        paths.preSequentialAlwaysDAGs.push_back({-1, {nodes}});
      }

      if (subgraphHasCombinationalInput(nodes, g) &&
          subgraphHasSequentialInput(nodes, g) &&
          subgraphHasCombinationalOutput(nodes, g)) {
        // Need to split up graphs of this form
        paths.postSequentialAlwaysDAGs.push_back({-1, {nodes}});
      }

      //if (subgraphHasAllSequentialOutputs(nodes, g)) {
      if (subgraphHasSequentialOutput(nodes, g)) {
        paths.preSequentialDAGs.push_back({-1, {nodes}});
      }

      //if (subgraphHasAllSequentialInputs(nodes, g)) {
      if (subgraphHasSequentialInput(nodes, g)) {
        paths.postSequentialDAGs.push_back({-1, {nodes}});
      }
      
      if (subgraphHasAllCombinationalInputs(nodes, g) &&
          subgraphHasAllCombinationalOutputs(nodes, g)) {
        paths.pureCombDAGs.push_back({-1, {nodes}});
      }
    }
    

    return paths;
  }

  vector<SIMDGroup> deleteDuplicates(const std::vector<SIMDGroup>& allUpdates) {
    vector<SIMDGroup> unique;

    for (auto& update : allUpdates) {

      bool isDuplicate = false;
      for (auto& existing : unique) {
        if (existing.nodes.size() != update.nodes.size()) {
          continue;
        }

        if (existing.nodes.size() == 1) {
          set<vdisc> ex_set(begin(existing.nodes[0]), end(existing.nodes[0]));
          set<vdisc> up_set(begin(update.nodes[0]), end(update.nodes[0]));

          if ((intersection(ex_set, up_set).size() == ex_set.size()) &&
              (ex_set.size() == up_set.size())) {
            isDuplicate = true;
            break;
          }
        }
      }

      if (!isDuplicate) {
        unique.push_back(update);
      }
    }
    return unique;
  }

  vector<SIMDGroup> pruneSequentialSinks(const std::vector<SIMDGroup> dags,
                                         const NGraph& g) {
    vector<SIMDGroup> gp;

    for (auto& dag : dags) {
      if (dag.nodes.size() == 1) {
        SubDAG sd;

        for (auto& node : dag.nodes[0]) {
          WireNode wd = g.getNode(node);
          if (!(wd.isSequential && wd.isReceiver)) {
            sd.push_back(node);
          } else {
            cout << "Removing " << nodeString(wd) << endl;
          }
        }

        bool deleted = true;
        while (deleted) {
          deleted = false;

          vdisc toDelete = 0;
          for (auto& node : sd) {
            WireNode wd = g.getNode(node);


            if (!isGraphOutput(wd) &&
                !(wd.isSequential && wd.isReceiver)) {
              // TODO: Make this the definition of isSubgraphOutput?
              bool isOut = true;

              for (auto& conn : g.outEdges(node)) {
                vdisc tg = g.target(conn);
                if (elem(tg, sd)) {
                  isOut = false;
                  break;
                }
              }

              if (isOut) {
                deleted = true;
                toDelete = node;
                break;
              }
            }
          }

          if (deleted) {
            cout << "Deleting " << nodeString(g.getNode(toDelete)) << endl;
            remove(toDelete, sd);
          }
        }

        gp.push_back({dag.totalWidth, {sd}});
      } else {
        gp.push_back(dag);
      }
    }

    return gp;
  }
  
  vector<SIMDGroup> pruneOutputs(const std::vector<SIMDGroup> dags,
                                 const NGraph& g) {
    vector<SIMDGroup> gp;

    for (auto& dag : dags) {
      if (dag.nodes.size() == 1) {
        SubDAG sd;

        for (auto& node : dag.nodes[0]) {
          WireNode wd = g.getNode(node);
          if (!isGraphOutput(wd)) {
            sd.push_back(node);
          }
        }

        bool deleted = true;
        while (deleted) {
          deleted = false;

          vdisc toDelete = 0;
          for (auto& node : sd) {
            WireNode wd = g.getNode(node);

            if (!isGraphOutput(wd) &&
                !(wd.isSequential && wd.isReceiver)) {
              bool isOut = true;

              for (auto& conn : g.outEdges(node)) {
                vdisc tg = g.target(conn);
                if (elem(tg, sd)) {
                  isOut = false;
                  break;
                }
              }

              if (isOut) {
                deleted = true;
                toDelete = node;
                break;
              }
            }
          }

          if (deleted) {
            remove(toDelete, sd);
          }
        }

        gp.push_back({dag.totalWidth, {sd}});
      } else {
        gp.push_back(dag);
      }
    }

    return gp;
  }


  SubDAG addInputs(const SubDAG& dag, const NGraph& g) {
    SubDAG fulldag;
    for (auto& vd : dag) {
      cout << "Node: " << g.getNode(vd).getWire()->toString() << endl;
      cout << "# of in edges = " << g.inEdges(vd).size() << endl;
      for (auto& con : g.inEdges(vd)) {
        vdisc src = g.source(con);

        cout << g.getNode(src).getWire()->toString();
        cout << ", type = " << *(g.getNode(src).getWire()->getType()) << endl;

        if (isGraphInput(g.getNode(src)) &&
            !isClkIn(*(g.getNode(src).getWire()->getType())) &&
            !elem(src, fulldag)) {
          cout << "Adding " << g.getNode(src).getWire()->toString() << endl;
          fulldag.push_back(src);
        }
      }

      fulldag.push_back(vd);
    }
    return fulldag;
  }

  SubDAG addConstants(const SubDAG& dag, const NGraph& g) {
    SubDAG fulldag;
    for (auto& vd : dag) {
      cout << "Node: " << g.getNode(vd).getWire()->toString() << endl;
      cout << "# of in edges = " << g.inEdges(vd).size() << endl;
      for (auto& con : g.inEdges(vd)) {
        vdisc src = g.source(con);

        cout << g.getNode(src).getWire()->toString();
        cout << ", type = " << *(g.getNode(src).getWire()->getType()) << endl;

        if (isConstant(g.getNode(src)) &&
            !isClkIn(*(g.getNode(src).getWire()->getType())) &&
            !elem(src, fulldag)) {
          cout << "Adding " << g.getNode(src).getWire()->toString() << endl;
          fulldag.push_back(src);
        }
      }

      fulldag.push_back(vd);
    }
    return fulldag;
  }

  bool allSameSize(const std::vector<SubDAG>& dags) {
    if (dags.size() < 2) {
      return true;
    }

    uint size = dags[0].size();
    for (uint i = 1; i < dags.size(); i++) {
      if (dags[i].size() != size) {
        return false;
      }
    }

    return true;
  }

  bool nodesMatch(const vdisc ref,
                  const vdisc a,
                  const NGraph& g) {
    WireNode rn = g.getNode(ref);
    WireNode an = g.getNode(a);

    if (isGraphInput(rn) && isGraphInput(an)) {
      // TODO: Check width
      return true;
    }

    if (isGraphOutput(rn) && isGraphOutput(an)) {
      // TODO: Check width
      return true;
    }

    if (isInstance(rn.getWire()) && isInstance(an.getWire())) {
      if (isRegisterInstance(rn.getWire()) &&
          isRegisterInstance(an.getWire())) {
        return true;
      }

      if (!isRegisterInstance(rn.getWire()) &&
          !isRegisterInstance(an.getWire())) {
        Instance* ri = toInstance(rn.getWire());
        Instance* ai = toInstance(an.getWire());

        if (getQualifiedOpName(*ri) ==
            getQualifiedOpName(*ai)) {
          return true;
        }
      }

    }

    return false;
  }
  
  SubDAG alignWRT(const SubDAG& reference,
                  const SubDAG& toAlign,
                  const NGraph& g) {
    set<vdisc> alreadyUsed;

    map<vdisc, vdisc> nodeMap;
    for (auto& refNode : reference) {

      bool foundMatch = false;
      for (auto& aNode : toAlign) {
        if (!elem(aNode, alreadyUsed) &&
            nodesMatch(refNode, aNode, g)) {
          nodeMap.insert({refNode, aNode});
          foundMatch = true;
          alreadyUsed.insert(aNode);
          break;
        }
      }

      if (!foundMatch) {
        return {};
      }
    }

    SubDAG aligned;
    for (auto& node : reference) {
      aligned.push_back(nodeMap[node]);
    }

    return aligned;
  }
                            
  vector<vector<SubDAG> >
  alignIdenticalGraphs(const std::vector<SubDAG>& dags,
                       const NGraph& g) {

    vector<vector<SubDAG> > eqClasses;

    if (dags.size() == 0) {
      return eqClasses;
    }
    
    vector<SubDAG> subdags;
    subdags.push_back(dags[0]);
    eqClasses.push_back(subdags);

    
    for (uint i = 1; i < dags.size(); i++) {

      bool foundClass = false;

      for (auto& eqClass : eqClasses) {
        SubDAG aligned = alignWRT(eqClass.back(), dags[i], g);

        // If the alignment succeeded add to existing equivalence class
        if (aligned.size() == dags[i].size()) {
          eqClass.push_back(aligned);
          foundClass = true;
          break;
        }
      }

      if (!foundClass) {
        eqClasses.push_back({dags[i]});
      }
    }

    return eqClasses;
  }

  std::vector<SIMDGroup>
  optimizeSIMD(const std::vector<SIMDGroup>& originalGroups,
               NGraph& g,
               Module& mod,
               LayoutPolicy& layoutPolicy) {

    if (originalGroups.size() == 0) {
      return originalGroups;
    }

    vector<SubDAG> dags;
    for (auto& gp : originalGroups) {
      if (gp.nodes.size() != 1) {
        return originalGroups;
      }

      dags.push_back(gp.nodes[0]);
    }

    cout << "Optimizing SIMD, found dag group of size " << dags.size() << endl;
    cout << "Dag size = " << dags[0].size() << endl;

    if (allSameSize(dags) && (dags.size() > 4) && (dags[0].size() == 2)) {
      cout << "Found " << dags.size() << " of size 2!" << endl;

      vector<SubDAG> fulldags;
      for (auto& dag : dags) {
        fulldags.push_back(addInputs(dag, g));
      }

      cout << "Full dags" << endl;
      for (auto& dag : fulldags) {
        cout << "===== DAG" << endl;
        for (auto& vd : dag) {
          cout << g.getNode(vd).getWire()->toString() << endl;
        }
      }

      // Note: Add graph input completion
      vector<vector<SubDAG> > eqClasses =
        alignIdenticalGraphs(fulldags, g);

      cout << "Aligned identical graphs" << endl;
      for (auto& subdags : eqClasses) {
        cout << "====== Class" << endl;
        for (auto& dag : subdags) {
          cout << "------- DAG" << endl;
          for (auto& vd : dag) {
            cout << g.getNode(vd).getWire()->toString() << endl;
          }
        }
      }

      int opWidth = 16;
      // Max logic op size is 128
      int groupSize = 128 / opWidth;

      cout << "Printing groups " << endl;

      vector<SIMDGroup> simdGroups;
      for (auto& eqClass : eqClasses) {
        auto group0 = groupIdenticalSubDAGs(eqClass, g, groupSize, layoutPolicy);
        concat(simdGroups, group0);
      }

      return simdGroups;
    }

    cout << "Nope, could not do SIMD optimizations" << endl;
    return originalGroups;
  }

  
}
