#include "multithreading.hpp"

using namespace CoreIR;
using namespace std;

namespace CoreIR {

  set<vdisc> connectedComponent(const vdisc v, NGraph& gr) {
    set<vdisc> cc;

    vector<vdisc> rem{v};

    while (rem.size() > 0) {
      vdisc nextNode = rem.back();
      rem.pop_back();

      cc.insert(nextNode);

      for (auto& ed : gr.inEdges(nextNode)) {
        vdisc other = gr.source(ed);
        vdisc thisN = gr.target(ed);

        assert(thisN == nextNode);

        if (cc.find(other) == end(cc)) {
          WireNode wd = gr.getNode(other);
          if (!isGraphInput(wd)) {
            rem.push_back(other);
          }
        }
      }

      for (auto& ed : gr.outEdges(nextNode)) {
        vdisc other = gr.target(ed);
        if (cc.find(other) == end(cc)) {
          WireNode wd = gr.getNode(other);
          if (!isGraphInput(wd)) {
            rem.push_back(other);
          }
          //rem.push_back(other);
        }
      }
    
    }

    return cc;
  }

  void balancedComponentsParallel(NGraph& gr) {
    set<vdisc> nodes;
    for (auto& vd : gr.getVerts()) {
      nodes.insert(vd);
    }

    int numComponents = 0;

    vector<set<vdisc> > ccs;
    for (auto& vd : gr.getVerts()) {

      WireNode wd = gr.getNode(vd);

      if (!isGraphInput(wd)) {
        if (nodes.find(vd) != end(nodes)) {
          set<vdisc> ccNodes =
            connectedComponent(vd, gr);

          //cout << "CC size = " << ccNodes.size() << endl;

          for (auto& ccNode : ccNodes) {
            nodes.erase(ccNode);

            WireNode w = gr.getNode(ccNode);
            w.setThreadNo(numComponents);
            gr.addVertLabel(ccNode, w);
          }
      

          ccs.push_back(ccNodes);
          numComponents++;
        }
      }
    }

    cout << "# of connected components = " << numComponents << endl;

    // Now balance the components
    //int nThreads = 2;
    int i = 0;
    for (auto& cc : ccs) {
      for (auto& vd : cc) {
        WireNode w = gr.getNode(vd);
        //w.setThreadNo((i % 2) + 1);
        w.setThreadNo((i % 2) + 1); 
        gr.addVertLabel(vd, w);
      }
      i++;
    }
  }
  
}
