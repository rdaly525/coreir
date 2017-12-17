#include "coreir/simulator/dag_optimization.h"

#include "coreir/simulator/multithreading.h"

using namespace std;

namespace CoreIR {

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
  
  
}
