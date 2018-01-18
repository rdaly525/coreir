#include "coreir/simulator/multithreading.h"

using namespace CoreIR;
using namespace std;

namespace CoreIR {

  int numThreads(const ThreadGraph& g) {
    return g.numVertices();
  }

  bool connectionFromTo(const vdisc sourceThread,
                        const vdisc destThread,
                        const NGraph& opG,
                        unordered_map<vdisc, vector<vdisc> >& threadComps) {
    vector<vdisc> sourceNodes = threadComps[sourceThread];
    vector<vdisc> destNodes = threadComps[destThread];
    sort(begin(destNodes), end(destNodes));

    for (auto& sn : sourceNodes) {

      for (auto ed : opG.outEdges(sn)) {
        if (binary_search(begin(destNodes), end(destNodes), opG.target(ed))) {
          return true;
        }
      }

    }

    return false;
  }
  
  set<vdisc> connectedComponent(const vdisc v, const NGraph& gr) {
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
          if (!isGraphInput(wd) && !isConstant(wd)) {
            rem.push_back(other);
          }
        }
      }

      for (auto& ed : gr.outEdges(nextNode)) {
        vdisc other = gr.target(ed);
        if (cc.find(other) == end(cc)) {
          WireNode wd = gr.getNode(other);
          if (!isGraphInput(wd) && !isConstant(wd)) {
            rem.push_back(other);
          }
        }
      }
    
    }

    return cc;
  }

  std::vector<std::set<vdisc>>
  connectedComponentsIgnoringInputs(const NGraph& gr) {
    set<vdisc> nodes;
    for (auto& vd : gr.getVerts()) {
      nodes.insert(vd);
    }

    vector<set<vdisc> > ccs;
    for (auto& vd : gr.getVerts()) {

      WireNode wd = gr.getNode(vd);

      if (!isGraphInput(wd) && !isConstant(wd)) {
        if (nodes.find(vd) != end(nodes)) {
          set<vdisc> ccNodes =
            connectedComponent(vd, gr);

          //cout << "CC size = " << ccNodes.size() << endl;

          for (auto& ccNode : ccNodes) {
            nodes.erase(ccNode);

            // WireNode w = gr.getNode(ccNode);
            // w.setThreadNo(numComponents);
            // gr.addVertLabel(ccNode, w);
          }
      

          ccs.push_back(ccNodes);
          //numComponents++;
        }
      }
    }

    return ccs;
  }

  void numberComponents(const std::vector<set<vdisc>>& ccs,
                        NGraph& gr) {
    int numComponents = 0;

    for (auto& ccNodes : ccs) {
      for (auto& ccNode : ccNodes) {
        WireNode w = gr.getNode(ccNode);
        w.setThreadNo(numComponents);
        gr.addVertLabel(ccNode, w);
      }
      numComponents++;
    }
    
  }

  void balancedComponentsParallel(NGraph& gr) {

    auto ccs = connectedComponentsIgnoringInputs(gr);
    cout << "# of connected components = " << ccs.size() << endl;

    numberComponents(ccs, gr);
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

  ThreadGraph buildThreadGraph(const NGraph& opG) {

    cout << "Building thread graph" << endl;

    ThreadGraph tg;

    unordered_map<vdisc, vector<vdisc> > threadComps;

    int i = 0;
    for (auto& v : opG.getVerts()) {
      int threadNo = opG.getNode(v).getThreadNo();

      auto tgVerts = tg.getVerts();
      if (!elem(threadNo, tgVerts)) {

        tg.addVertex( threadNo );

      } 

      map_insert(threadComps, threadNo, v);

      if ((i % 1000) == 0) {
        cout << "Computed thread for vertex " << i << ", # of thread nos = " << tg.getVerts().size() << endl;
      }

      i++;
    }

    cout << "Thread components" << endl;
    for (auto& ent : threadComps) {
      cout << "thread number " << ent.first << " contains " << ent.second.size() << " nodes" << endl;
     //  for (auto& vd : ent.second) {
     // cout << "\t" << vd << " = " << opG.getNode(vd).getWire()->toString() << endl;
     //  }
    }

    // cout << "Operation graph edges" << endl;
    // for (auto& ed : opG.getEdges()) {
    //   cout << "edge " << ed << " = " << opG.source(ed) << " --> " << opG.target(ed) << endl;
    // }

    // for (auto& src : opG.getVerts()) {
    //   for (auto& dest : opG.getVerts()) {
    //  cout << src << " connected to " << dest << " ? " << opG.connected(src, dest) << endl;
    //   }
    // }

    cout << "# of threadComps = " << threadComps.size() << endl;

    // Add edges to graph
    vector<vdisc> threadVerts = tg.getVerts();

    cout << "# of threadVerts = " << threadVerts.size() << endl;

    for (uint i = 0; i < threadVerts.size(); i++) {
      for (uint j = 0; j < threadVerts.size(); j++) {
        if (i != j) {
          vdisc sourceThread = threadVerts[i];
          vdisc destThread = threadVerts[j];

          // There are no backward connections
          //if (!tg.connected(destThread, sourceThread)) {

            if (connectionFromTo(sourceThread, destThread, opG, threadComps)) {
              cout << "Adding edge from " << sourceThread << " to " << destThread << endl;
              tg.addEdge(sourceThread, destThread);
            }

            //}
        }
        
      }
    }

    cout << "# of verts = " << tg.getVerts().size() << endl;
    cout << "# of edges = " << tg.getEdges().size() << endl;
    for (auto& ed : tg.getEdges()) {
      cout << "edge " << ed << " = " << tg.source(ed) << " --> " << tg.target(ed) << endl;
    }
      
    return tg;
  }

  
}
