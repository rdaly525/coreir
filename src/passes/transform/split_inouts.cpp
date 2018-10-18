#include "coreir.h"
#include "coreir/passes/transform/split_inouts.h"

using namespace std;
using namespace CoreIR;

void splitInOutToTribuf(const std::string& portName,
                        CoreIR::Select* const inputPort,
                        CoreIR::Select* const outputPort,
                        Module* const module,
                        ModuleDef* const def) {

  Context* c = def->getContext();

  Wireable* self = module->getDef()->sel("self");

  Select* ioPort = self->sel(portName);
  
  vector<Select*> ios = getIOSelects(ioPort);
  set<Instance*> ioSources;
  for (auto io : ios) {
    Wireable* src = extractSource(io);
    assert(isa<Instance>(src));

    ioSources.insert(cast<Instance>(src));
  }
  
  int width = 1;
  auto mux = def->addInstance(portName + "_split_mux",
                              "coreir.mux",
                              {{"width", Const::make(c, width)}});

  // Add array connections
  def->connect(mux->sel("in0")->sel(0), inputPort);

  Instance* tristateBuf = nullptr;
  Instance* tristateCast = nullptr;

  cout << "IO sources" << endl;
  for (auto ioSrc : ioSources) {
    cout << "\t" << ioSrc->toString() << endl;

    if (getQualifiedOpName(*ioSrc) == "coreir.tribuf") {
      tristateBuf = ioSrc;
    } else if (getQualifiedOpName(*ioSrc) == "coreir.ibuf") {
      tristateCast = ioSrc;
    }
  }

  // Note: Need to check whether the connections between inouts are full
  // connections or partial as well

  assert(tristateBuf != nullptr);
  assert(tristateCast != nullptr);

  // tristateBuffer inputs to mux in1
  auto triBufConns = getSourceConnections(tristateBuf->sel("in"));
  cout << "Tristatebuf conns size = " << triBufConns.size() << endl;
  for (auto conn : triBufConns) {
    cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
    Wireable* f = replaceSelect(tristateBuf->sel("in"),
                                mux->sel("in1"),
                                conn.first);

    Wireable* s = replaceSelect(tristateBuf->sel("in"),
                                mux->sel("in1"),
                                conn.second);

    def->connect(f, s);
  }

  vector<Select*> tribufSels = getSourceSelects(tristateBuf->sel("in"));
  // TODO: Eventually support arbitrary width connections
  assert(tribufSels.size() == 1);

  auto triBufDriver = tribufSels[0];
  def->connect(triBufDriver, outputPort);

  // Wire tricast output receivers to the triput output receivers to
  // the mux output
  //auto triBufConns = getSourceConnections(tristateBuf->sel("in"));
  //cout << "Tristatebuf conns size = " << triBufConns.size() << endl;
  auto triCastConns = getReceiverConnections(tristateCast->sel("out"));
  cout << "Tri cast conns = " << triCastConns.size() << endl;
  vector<Connection> freshConns;
  for (auto conn : triCastConns) {
    cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
    Wireable* f = replaceSelect(tristateCast->sel("out"),
                                mux->sel("out"),
                                conn.first);

    Wireable* s = replaceSelect(tristateCast->sel("out"),
                                mux->sel("out"),
                                conn.second);

    freshConns.push_back({f, s});
  }

  for (auto conn : triCastConns) {
    def->disconnect(conn);
  }

  for (auto conn : freshConns) {
    def->connect(conn.first, conn.second);
  }

  // tristateBuf en to mux select
  auto enSels = getSourceSelects(tristateBuf->sel("en"));
  assert(enSels.size() == 1);
      
  def->connect(mux->sel("sel"), enSels[0]);

  def->removeInstance(tristateBuf);
  def->removeInstance(tristateCast);
}

bool Passes::SplitInouts::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* module = node.getModule();

  if (!module->hasDef()) {
    return false;
  }

  cout << "Processing module = " << module->getName() << endl;
  //module->print();
  
  Context* c = module->getDef()->getContext();

  bool changed = false;
  
  map<Select*, Select*> inoutsToOuts;
  map<Select*, Select*> inoutsToIns;
  for (auto field : module->getType()->getRecord()) {
    if (field.second->getDir() == Type::DK_InOut) {
      // TODO: Actually change the underlying array type instead
      // of just assuming its BitInOut
      string portName = field.first;
      string input = portName + "_input";
      string output = portName + "_output";

      node.appendField(input, c->BitIn());
      node.appendField(output, c->Bit());

      Wireable* self = module->getDef()->sel("self");

      Select* ioPort = self->sel(portName);
      Select* inputPort = self->sel(input);
      Select* outputPort = self->sel(output);

      cout << ioPort->toString() << endl;
      cout << inputPort->toString() << endl;
      cout << outputPort->toString() << endl;

      auto def = module->getDef();

      // Get all connections
      vector<Select*> srcs = getSourceSelects(ioPort);
      assert(srcs.size() == 0);
      
      vector<Select*> receivers = getReceiverSelects(ioPort);
      assert(receivers.size() == 0);

      vector<Select*> ios = getIOSelects(ioPort);
      cout << "# of IO selects = " << ios.size() << endl;
      for (auto io : ios) {
        cout << "\t" << io->toString() << endl;
      }

      set<Instance*> ioSources;
      for (auto io : ios) {
        Wireable* src = extractSource(io);
        assert(isa<Instance>(src));

        ioSources.insert(cast<Instance>(src));
      }

      if (ioSources.size() == 2) {

        splitInOutToTribuf(portName, inputPort, outputPort, module, def);

        changed = true;
      } else {
        assert(ioSources.size() == 1);
        assert(ios.size() == 1);

        Select* innerIOPort = *begin(ios);

        cout << "innerIOPort connected to this module is " << innerIOPort->toString() << endl;

        auto srcInst = innerIOPort->getTopParent();
        assert(isa<Instance>(srcInst));

        Instance* innerInstance = cast<Instance>(srcInst);
        cout << "Inner instance is " << innerInstance->toString() << endl;

        assert(isBitType(*(innerIOPort->getType())));
        
        string ioSel = innerIOPort->getSelStr();

        string innerInputStr = ioSel + "_input";
        string innerOutputStr = ioSel + "_output";

        Select* innerInput = innerInstance->sel(innerInputStr);
        Select* innerOutput = innerInstance->sel(innerOutputStr);

        def->disconnect(ioPort);

        def->connect(inputPort, innerInput);
        def->connect(outputPort, innerOutput);

        //assert(false);

        changed = true;
      }
    }
  }
  
  return changed;
}
