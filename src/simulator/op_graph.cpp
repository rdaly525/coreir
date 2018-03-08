#include "coreir/simulator/op_graph.h"

#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/utils.h"

using namespace std;

namespace CoreIR {

  void addConnection(std::unordered_map<WireNode, vdisc>& imap,
		     Conn& conn,
		     NGraph& g);
  
  Wireable* extractSource(Select* sel) {
    Wireable* p = sel->getParent();

    // Every select off of self gets its own node
    if (fromSelf(sel) && (!isSelect(p))) {
      return sel;
    }

    // Base case for non self connections.
    if (!isSelect(p)) {
      return p;
    }

    return extractSource(toSelect(p));
  }
  
  WireNode getNode(const NGraph& g, const vdisc vd) {
    return g.getNode(vd);
  }

  Conn getConn(const NGraph& g, const edisc ed) {
    return g.getConn(ed);
  }

  std::vector<Conn> getInputConnections(const vdisc vd, const NGraph& g) {
    return g.getInputConnections(vd);
  }

  std::vector<Conn> NGraph::getInputConnections(const vdisc vd) const {
    vector<Conn> inConss;

    Wireable* w = getNode(vd).getWire();

    for (auto out_edge_desc : inEdges(vd)) {

      if (hasLabel(out_edge_desc)) {
	Conn edge_conn =
	  getConn(out_edge_desc);

	assert(isSelect(edge_conn.second.getWire()));

	CoreIR::Select* sel = static_cast<Select*>(edge_conn.second.getWire());

	assert(extractSource(sel) == w);

	inConss.push_back(edge_conn);
      }
    }
  
    return inConss;

  }

  std::vector<Wireable*> NGraph::getOutputs(const vdisc vd) const {
    vector<Wireable*> outputs;

    Wireable* w = getNode(vd).getWire();

    for (auto out_edge_desc : outEdges(vd)) {

      Conn edge_conn =
	getConn(out_edge_desc);

      assert(isSelect(edge_conn.first.getWire()));
      Select* sel = static_cast<Select*>(edge_conn.first.getWire());
      assert(sel->getParent() == w);

      outputs.push_back(edge_conn.second.getWire());
      
    }

    return outputs;
  }
  
  std::vector<Wireable*> getOutputs(const vdisc vd, const NGraph& g) {
    return g.getOutputs(vd);
  }

  std::vector<Wireable*> NGraph::getInputs(const vdisc vd) const {
    vector<Wireable*> inputs;
    Wireable* w = getNode(vd).getWire();

    for (auto in_edge_desc : inEdges(vd)) {

      Conn edge_conn =
	getConn(in_edge_desc);

      assert(isSelect(edge_conn.second.getWire()));

      Select* sel = static_cast<Select*>(edge_conn.second.getWire());

      assert(extractSource(sel) == w); //->getParent() == w);

      inputs.push_back(edge_conn.first.getWire());
      
    }

    return inputs;

  }

  std::vector<Wireable*> getInputs(const vdisc vd, const NGraph& g) {
    return g.getInputs(vd);
  }

  vector<vdisc> vertsWithNoIncomingEdge(const NGraph& g) {
    return g.vertsWithNoIncomingEdge();
  }

  vector<vdisc> NGraph::vertsWithNoIncomingEdge() const {
    vector<vdisc> vs;


    for (auto v : getVerts()) {

      //if (getInputConnections(v).size() == 0) {
      if (inEdges(v).size() == 0) {
	vs.push_back(v);
      }
    }

    return vs;
    
  }

  int numVertices(const NGraph& g) {
    return g.numVertices();
  }

  std::vector<std::vector<vdisc> > topologicalLevels(const NGraph& g) {
    vector<vector<vdisc> > levels;

    auto allVerts = g.getVerts();
    set<vdisc> nodes(begin(allVerts), end(allVerts));
    set<vdisc> alreadyAdded;

    vector<vdisc> initial = vertsWithNoIncomingEdge(g);
    for (auto& node : initial) {
      nodes.erase(node);
      alreadyAdded.insert(node);
    }

    levels.push_back(initial);

    while (nodes.size() > 0) {
      vector<vdisc> level;

      for (auto& node : nodes) {
        auto inEds = g.inEdges(node);
        if (inEds.size() > 0) {

          bool allInputsInPriorLevel = true;
          for (auto& inEd : inEds) {
            vdisc src = g.source(inEd);
            if (alreadyAdded.find(src) == end(alreadyAdded)) {
              allInputsInPriorLevel = false;
              break;
            }
          }

          if (allInputsInPriorLevel) {
            level.push_back(node);
          }
        }
      }

      for (auto& node : level) {
        nodes.erase(node);
        alreadyAdded.insert(node);
      }

      levels.push_back(level);
    }

    assert(alreadyAdded.size() == g.getVerts().size());

    return levels;
  }

  std::deque<vdisc> topologicalSortNoFail(const NGraph& g) {
    deque<vdisc> topo_order;

    vector<vdisc> s = vertsWithNoIncomingEdge(g);

    //vector<edisc> deleted_edges;
    unordered_set<edisc> deleted_edges;

    cout << "Starting topological sort" << endl;

    while (s.size() > 0) {
      vdisc vd = s.back();

      //assert(!elem(vd, topo_order));

      topo_order.push_back(vd);
      s.pop_back();

      
      for (auto ed : g.outEdges(vd)) {

	//deleted_edges.push_back(ed);
	deleted_edges.insert(ed);
	
	vdisc src = g.source(ed);
	vdisc dest = g.target(ed);

	assert(src == vd);

	bool noOtherEdges = true;

	for (auto in_ed : g.inEdges(dest)) {

	  if (!elem(in_ed, deleted_edges)) {
	    noOtherEdges = false;
	    break;
	  }
	}

	if (noOtherEdges){

	  //assert(!elem(dest, s));

	  s.push_back(dest);
	}
      }


    }

    cout << "topo_order.size() = " << topo_order.size() << endl;
    cout << "numVertices(g)    = " << numVertices(g) << endl;

    return topo_order;
  }

  std::deque<vdisc> topologicalSort(const NGraph& g) {

    auto topo_order = topologicalSortNoFail(g);
    // cout << "Topological order" << endl;
    // for (auto& vd : topo_order) {
    //   cout << vd << endl;
    // }


    if (!(topo_order.size() == (uint) numVertices(g))) {
      cout << "Vertices not all included!" << endl;

      for (auto vert : g.getVerts()) {
        if (!elem(vert, topo_order)) {
          cout << "\tNot in topological sort: " << vert << ", " << g.getNode(vert).getWire()->toString() << ", " << g.getNode(vert).getWire()->getType()->toString() << endl;
          cout << "\tOUTPUT CONNECTIONS" << endl;
          for (auto ed : g.outEdges(vert)) {
            Conn c = g.getConn(ed);
            cout << "\t\t" << c.first.getWire()->toString() << " <---> " << c.second.getWire()->toString() << endl;
              
          }

          cout << "\tINPUT CONNECTIONS" << endl;
          for (auto ed : g.inEdges(vert)) {
            Conn c = g.getConn(ed);
            cout << "\t\t" << c.first.getWire()->toString() << " <---> " << c.second.getWire()->toString() << endl;
            //cout << "\t\t" << nodeString(g.getNode(c.first)) << " <---> " << nodeString(g.getNode(c.second)) << endl;
              
          }
          
        }
      }
      assert(topo_order.size() == (uint) numVertices(g));
    }

    return topo_order;
  }

  std::vector<Conn> getOutputConnections(const vdisc vd, const NGraph& g) {
    return g.getOutputConnections(vd);
  }

  std::vector<Conn> NGraph::getOutputConnections(const vdisc vd) const {
    vector<Conn> outConns;

    Wireable* w = getNode(vd).getWire();

    for (auto out_edge_desc : outEdges(vd)) {

      Conn edge_conn =
        getConn(out_edge_desc);

      assert(isSelect(edge_conn.first.getWire()));

      Select* sel = static_cast<Select*>(edge_conn.first.getWire());

      assert(extractSource(sel) == w);
      //assert(sel->getParent() == w);

      outConns.push_back(edge_conn);
      
    }
  
    return outConns;
  }


  void addConnection(unordered_map<WireNode, vdisc>& imap,
		     Conn& conn,
		     NGraph& g) {

    assert(isSelect(conn.first.getWire()));
    assert(isSelect(conn.second.getWire()));

    auto c1 = static_cast<Select*>(conn.first.getWire());
    auto c2 = static_cast<Select*>(conn.second.getWire());

    Wireable* p1 = extractSource(c1);

    vdisc c1_disc;
    // if (isRegisterInstance(p1) ||
    //     isMemoryInstance(p1) ||
    //     isDFFInstance(p1)) {
    //   auto c1_disc_it = imap.find(outputNode(p1));

    //   assert(c1_disc_it != imap.end());

    //   c1_disc = (*c1_disc_it).second;

    // } else {
    //   assert(!isRegisterInstance(p1));

      auto c1_disc_it = imap.find(combNode(p1));

      if (isRegisterInstance(p1) ||
          isMemoryInstance(p1) ||
          isDFFInstance(p1)) {
        c1_disc_it = imap.find(outputNode(p1));
      }

      assert(c1_disc_it != imap.end());

      c1_disc = (*c1_disc_it).second;
      //}
      
    Wireable* p2 = extractSource(c2);

    vdisc c2_disc;
    // NOTE: If the receiver instance node is memory and the
    // port that is being received is the raddr then the
    // sourceNode receives it
    if (isMemoryInstance(p2)) {

      auto c2_disc_it = imap.find(receiverNode(p2));

      if (c2->getSelStr() == "raddr") {
        cout << "Found raddr" << endl;
        c2_disc_it = imap.find(outputNode(p2));

        assert(c2_disc_it != imap.end());

        c2_disc = (*c2_disc_it).second;

      } else {
        auto c2_disc_it = imap.find(combNode(p2));

        if (isRegisterInstance(p2) ||
            isMemoryInstance(p2) ||
            isDFFInstance(p2)) {
          c2_disc_it = imap.find(receiverNode(p2));
        }
        
        assert(c2_disc_it != imap.end());

        c2_disc = (*c2_disc_it).second;

      }
    } else {

      auto c2_disc_it = imap.find(combNode(p2));
      if (isRegisterInstance(p2) ||
          isMemoryInstance(p2) ||
          isDFFInstance(p2)) {
        c2_disc_it = imap.find(receiverNode(p2));
      }

      assert(c2_disc_it != imap.end());

      c2_disc = (*c2_disc_it).second;
    }

    edisc ed = g.addEdge(c1_disc, c2_disc);

    g.addEdgeLabel(ed, conn);
  }

  void addWireableToGraph(Wireable* w1,
			  unordered_map<WireNode, vdisc>& imap,
			  NGraph& g) {

    if (isInstance(w1)) {
      Instance* inst = toInstance(w1);
      string genRefName = getInstanceName(*inst);

      if (isRegisterInstance(inst) ||
          isMemoryInstance(inst) ||
          isDFFInstance(inst)) {
	WireNode wOutput = outputNode(w1);
	WireNode wInput = receiverNode(w1);

	// bool setV1 = false;
	// bool setV2 = false;
	
	vdisc v1, v2;
	if (imap.find(wOutput) == end(imap)) {
	  v1 = g.addVertex(wOutput);
	  imap.insert({wOutput, v1});
	  //setV1 = true;
	}

	if (imap.find(wInput) == end(imap)) {
	  v2 = g.addVertex(wInput);
	  imap.insert({wInput, v2});
	  //setV2 = true;
	}

	// if (setV1 && setV2) {
	//   g.addEdge(v1, v2);
	// }

	return;
      }
    }

    if (imap.find(combNode(w1)) == end(imap)) {
      WireNode w = combNode(w1);

      vdisc v1 = g.addVertex(w);
      imap.insert({w, v1});
    }

  }

  vector<Conn> buildOrderedConnections(Module* mod) {
    vector<Conn> conns;

    assert(mod->hasDef());

    for (auto& connection : mod->getDef()->getConnections()) {

      assert(connectionIsOrdered(connection));

      Wireable* fst = connection.first;
      Wireable* snd = connection.second;

      assert(isSelect(fst));
      assert(isSelect(snd));

      Select* fst_select = static_cast<Select*>(fst);

      Type* fst_tp = fst_select->getType();

      InstanceValue w_fst(toSelect(fst));
      InstanceValue w_snd(toSelect(snd));

      if (fst_tp->isInput()) {
	conns.push_back({w_snd, w_fst});
      } else {
	conns.push_back({w_fst, w_snd});
      }

    }

    assert(conns.size() == mod->getDef()->getConnections().size());

    return conns;
  
  }

  void buildOrderedGraph(Module* mod, NGraph& g) {

    auto ord_conns = buildOrderedConnections(mod);

    // Add vertexes for all instances in the graph
    unordered_map<WireNode, vdisc> imap;

    for (auto& conn : ord_conns) {

      Select* sel1 = toSelect(conn.first.getWire());
      Select* sel2 = toSelect(conn.second.getWire());

      Wireable* w1 = extractSource(sel1);
      Wireable* w2 = extractSource(sel2);

      addWireableToGraph(w1, imap, g);
      addWireableToGraph(w2, imap, g);

    }

    // Add edges to the graph
    for (Conn conn : ord_conns) {
      addConnection(imap, conn, g);
    }

  }

  InstanceValue findArg(string argName, std::vector<Conn>& ins) {
    for (auto& conn : ins) {
      InstanceValue arg = conn.first;
      InstanceValue placement = conn.second;
      string selName = toSelect(placement.getWire())->getSelStr();
      if (selName == argName) {
	return arg;
      }
    }

    cout << "Error: Could not find argument: " << argName << endl;

    assert(false);
  }

  void setEdgeClean(const edisc ed,
		    NGraph& g) {
    Conn c = g.getConn(ed);

    Conn cleanConn;
    cleanConn.first = c.first;
    cleanConn.first.setNeedsMask(false);
    cleanConn.second = c.second;
    g.addEdgeLabel(ed, cleanConn);
  }

  bool inputsAreClean(const vdisc vd,
		      const NGraph& g) {
    for (auto& conn : g.getInputConnections(vd)) {
      if (conn.first.needsMask()) {
	return false;
      }
    }

    return true;
  }

  void eliminateMasks(const std::deque<vdisc>& topoOrder,
		      NGraph& g) {
    for (auto& vd : topoOrder) {
      WireNode opNode = g.getNode(vd);

      // Outputs from an input are all clean
      if (!isInstance(opNode.getWire())) {
	for (auto& ed : g.outEdges(vd)) {
	  setEdgeClean(ed, g);
	}
      } else {
	Instance* inst = toInstance(opNode.getWire());
	string name = getOpName(*inst);

	if ((name == "and") || (name == "or") || (name == "xor") ||
	    (name == "bitand") || (name == "bitand") ||
	    isUnsignedCmp(*inst) || isSignedCmp(*inst)) {
	  for (auto& ed : g.outEdges(vd)) {
	    setEdgeClean(ed, g);
	  }
	}
      }
    }
  }

  bool inputsNeedMasks(const WireNode& opNode) {
    Wireable* w = opNode.getWire();

    if (!isInstance(w)) {
      return false;
    }

    return true;
  }

  int numMasksNeeded(const NGraph& g) {
    int numMasks = 0;

    for (auto& vd : g.getVerts()) {

      WireNode opNode = g.getNode(vd);

      // Inputs do not need to be masked
      if (isInstance(opNode.getWire())) {
	vector<Select*> alreadyCounted;
	for (auto& conn : g.getOutputConnections(vd)) {

	  if (!elem(conn.first.getWire(), alreadyCounted)) {
	    InstanceValue& in = conn.first;

	    if (in.needsMask()) {
	      numMasks++;
	    }

	    alreadyCounted.push_back(in.getWire());

	  }

	}
      }

    }

    return numMasks;
  }

  bool isThreadShared(const vdisc v, const NGraph& g) {
    int threadNo = g.getNode(v).getThreadNo();

    for (auto& conn : g.outEdges(v)) {
      vdisc dest = g.target(conn);
      if (g.getNode(dest).getThreadNo() != threadNo) {
	return true;
      }
    }

    return false;
  }

  Select* findMainClock(const NGraph& g) {
    vector<Select*> clockInputs;

    for (auto& vd : g.getVerts()) {

      WireNode w = g.getNode(vd);

      if (isGraphInput(w)) {

        Select* inSel = toSelect(w.getWire());
        Type* tp = inSel->getType();

        if (tp->getKind() == CoreIR::Type::TK_Named) {
          NamedType* ntp = static_cast<NamedType*>(tp);

          if (ntp->toString() == "coreir.clk") {
            clockInputs.push_back(inSel);
          }
        }

      }
      
    }

    if (clockInputs.size() > 1) {
      cout << "ERROR: Circuit has " << clockInputs.size() << " clocks, but this simulator currently supports only one" << endl;
      cout << "The clocks are " << endl;
      for (auto& clk : clockInputs) {
        cout << clk->toString() << endl;
      }
      assert(false);
    }

    if (clockInputs.size() == 0) {
      return nullptr;
    }

    return clockInputs[0];
  }

  bool isSubgraphInput(const vdisc vd,
                       const std::deque<vdisc>& nodes,
                       const NGraph& g) {

    if (g.inEdges(vd).size() == 0) {
      WireNode wd = g.getNode(vd);
      Wireable* src = wd.getWire();

      //cout << "src = " << src->toString() << endl;

      if (isInstance(src)) {
        Instance* inst = toInstance(src);
        if ((getQualifiedOpName(*inst) == "coreir.const") ||
            (getQualifiedOpName(*inst) == "corebit.const")) {
          return false;
        }
      }
    }

    for (auto ec : g.inEdges(vd)) {
      for (auto& other : nodes) {
        if (g.source(ec) == other) {
          return false;
        }
      }
    }

    return true;
  }

  bool isSubgraphOutput(const vdisc vd,
                       const std::deque<vdisc>& nodes,
                       const NGraph& g) {

    return g.outEdges(vd).size() == 0;
  }
  
  bool subgraphHasCombinationalInput(const std::deque<vdisc>& nodes,
                                     const NGraph& g) {
    bool hasCombInput = false;
    for (auto& vd : nodes) {
      if (isSubgraphInput(vd, nodes, g)) {

        WireNode wd = g.getNode(vd);
        if (!wd.isSequential) {
          hasCombInput = true;
          break;
        }
      }
    }

    return hasCombInput;
  }

  bool subgraphHasAllSequentialOutputs(const std::deque<vdisc>& nodes,
                                       const NGraph& g) {
    for (auto& vd : nodes) {
      if (isSubgraphOutput(vd, nodes, g)) {
        WireNode wd = g.getNode(vd);
        if (!wd.isSequential) {
          return false;
        }
      }
    }

    return true;
  }

  bool subgraphHasAllSequentialInputs(const std::deque<vdisc>& nodes,
                                      const NGraph& g) {
    for (auto& vd : nodes) {
      if (isSubgraphInput(vd, nodes, g)) {
        WireNode wd = g.getNode(vd);
        if (!wd.isSequential) {
          return false;
        }
      }
    }

    return true;
  }

  bool subgraphHasCombinationalOutput(const std::deque<vdisc>& nodes,
                                      const NGraph& g) {
    bool hasCombOutput = false;
    for (auto& vd : nodes) {
      if (isSubgraphOutput(vd, nodes, g)) {

        WireNode wd = g.getNode(vd);
        if (!wd.isSequential) {
          hasCombOutput = true;
          break;
        }
      }
    }

    return hasCombOutput;
  }

  bool subgraphHasSequentialInput(const std::deque<vdisc>& nodes,
                                  const NGraph& g) {

    for (auto& vd : nodes) {
      if (isSubgraphInput(vd, nodes, g)) {

        WireNode wd = g.getNode(vd);
        if (wd.isSequential) {
          return true;
        }
      }
    }

    return false;
  }

  bool subgraphHasSequentialOutput(const std::deque<vdisc>& nodes,
                                   const NGraph& g) {

    for (auto& vd : nodes) {
      if (isSubgraphOutput(vd, nodes, g)) {

        WireNode wd = g.getNode(vd);
        if (wd.isSequential) {
          return true;
        }
      }
    }

    return false;
  }

  bool subgraphHasAllCombinationalInputs(const std::deque<vdisc>& nodes,
                                         const NGraph& g) {
    return !subgraphHasSequentialInput(nodes, g);
  }

  bool subgraphHasAllCombinationalOutputs(const std::deque<vdisc>& nodes,
                                         const NGraph& g) {
    return !subgraphHasSequentialOutput(nodes, g);
  }


  bool isConstant(const WireNode& wd) {
    Wireable* w = wd.getWire();

    if (isInstance(w)) {
      string name = getQualifiedOpName(*toInstance(w));

      return (name == "coreir.const") ||
        (name == "corebit.const");
    }

    return false;
  }

}
