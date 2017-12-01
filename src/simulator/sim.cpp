#include "coreir/simulator/simulator.h"

#include "coreir/passes/transform/flatten.h"
#include "coreir/passes/transform/rungenerators.h"

#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/print_c.h"
#include "coreir/simulator/utils.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  static string lastClkVarName(InstanceValue& clk) {
    return cVar("(state->", clk, "_last)");
  }

  static string clkVarName(InstanceValue& clk) {
    return cVar("(state->", clk, ")");
  }
  
  static string outputVarName(CoreIR::Wireable& outSel) {
    return cVar("(state->", outSel, ")");
  }

  static string outputVarName(const InstanceValue& val) {
    return cVar("(state->", val, ")");
  }

  CoreIR::Select* baseSelect(CoreIR::Select* const sel) {
    if (!isSelect(sel->getParent())) {
      return sel;
    }

    return baseSelect(toSelect(sel->getParent()));
  }

  class CustomStructLayout : public LayoutPolicy {
  public:
    std::vector<std::pair<CoreIR::Type*, std::string> > varDecls;
    std::set<std::string> allocatedAlready;

    CoreIR::Context* c;

    CustomStructLayout(CoreIR::Context* const c_) : c(c_) {}

    void forceAdjacent(const std::vector<std::string>& vars) {
      vector<unsigned> adjacentInds;
      //for (auto& elem : varDecls) {
      for (auto& v : vars) {
        for (unsigned i = 0; i < varDecls.size(); i++) {
          auto& elem = varDecls[i];
          if (elem.second == v) {
            adjacentInds.push_back(i);
            break;
          }
        }
      }

      int oldSize = varDecls.size();

      auto adj = select_indexes(varDecls, adjacentInds);
      varDecls = copy_not_indexes(varDecls, adjacentInds);

      cout << "Mid size = " << varDecls.size() << endl;

      concat(varDecls, adj);

      cout << "Old size = " << oldSize << endl;
      cout << "New size = " << varDecls.size() << endl;

      cout << "After forcing adjacency for " << endl;
      for (auto& v : vars) {
        cout << v << endl;
      }

      cout << endl << "Layout order is " << endl;
      for (auto& elem : varDecls) {
        cout << elem.second << endl;
      }
      assert(varDecls.size() == oldSize);
    }

    std::string lastClkVarName(InstanceValue& clk) {
      varDecls.push_back({clk.getWire()->getType(), cVar("", clk, "_last")});
      return CoreIR::lastClkVarName(clk);
    }

    std::string clkVarName(InstanceValue& clk) {
      varDecls.push_back({clk.getWire()->getType(), cVar(clk)});
      return CoreIR::clkVarName(clk);
    }

    std::string selectName(CoreIR::Select* sel) {
      Select* baseSel = baseSelect(toSelect(sel));

      if (!elem(cVar(baseSel), allocatedAlready)) {
        varDecls.push_back({baseSel->getType(), cVar(baseSel)});
        allocatedAlready.insert(cVar(baseSel));
      }

      return CoreIR::outputVarName(sel);
    }

    std::string outputVarName(CoreIR::Wireable& val) {

      if (isSelect(val)) {
        return selectName(toSelect(&val));
      }

      assert(isInstance(&val));

      if (isRegisterInstance(&val)) {

        Select* sel = val.sel("out");
        if (!elem(cVar(val), allocatedAlready)) {
          varDecls.push_back({sel->getType(), cVar(val)});
          allocatedAlready.insert(cVar(val));
        }

        return CoreIR::outputVarName(val);
      } else if (isMemoryInstance(&val)) {

        if (!elem(cVar(val), allocatedAlready)) {
          Instance* is = toInstance(&val);

          Values args = is->getModuleRef()->getGenArgs();

          auto wArg = args["width"];
          auto dArg = args["depth"];
        
          uint width = wArg->get<int>();
          uint depth = dArg->get<int>();
          Type* elemType = c->Array(depth, c->Array(width, c->BitIn()));

          varDecls.push_back({elemType, cVar(val)});
          allocatedAlready.insert(cVar(val));
        }

        return CoreIR::outputVarName(val);
      }

      assert(false);
    }

    std::string outputVarName(const InstanceValue& val) {
      cout << "Creating output for " << val.getWire()->toString() << endl;

      return selectName(val.getWire());
    }
    
  };

  string printBinop(const WireNode& wd,
                    const vdisc vd,
                    const NGraph& g,
                    LayoutPolicy& lp);

  string printOpResultStr(const InstanceValue& wd,
                          const NGraph& g,
                          LayoutPolicy& lp);

  // wd is an instance node
  string opResultStr(const WireNode& wd,
                     const vdisc vd,
                     const NGraph& g,
                     LayoutPolicy& lp);

  string printUnop(Instance* inst,
                   const vdisc vd,
                   const NGraph& g,
                   LayoutPolicy& lp) {
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 1);

    Conn cn = (*std::begin(inConns));

    Wireable* dest = inConns[0].second.getWire();
    assert(isSelect(dest));

    Select* destSel = toSelect(dest);
    assert(destSel->getParent() == inst);

    string opString = getOpString(*inst);

    string val;

    if (opString != "andr") {
      val = opString + printOpResultStr(cn.first, g, lp);
    } else {

      uint w = typeWidth(*(cn.first.getWire()->getType()));
      val = parens(printOpResultStr(cn.first, g, lp) + " == " + bitMaskString(w));

    }

    string res =
      maskResult(*((outPair.second)->getType()),
                 val);

    return res;
  }

  string printBVConstant(Instance* inst, const vdisc vd, const NGraph& g) {

    bool foundValue = false;

    string argStr = "";
    for (auto& arg : inst->getModArgs()) {
      if (arg.first == "value") {
        foundValue = true;
        Value* valArg = arg.second;

        cout << "Value type = " << valArg->getValueType()->toString() << endl;

        BitVector bv = valArg->get<BitVector>();
        stringstream ss;
        ss << "0b" << bv;
        argStr = ss.str();
      }
    }

    assert(foundValue);

    return argStr;
  }

  string printBitConstant(Instance* inst, const vdisc vd, const NGraph& g) {

    bool foundValue = false;

    string argStr = "";
    for (auto& arg : inst->getModArgs()) {
      if (arg.first == "value") {
        foundValue = true;
        Value* valArg = arg.second;

        assert(valArg->getValueType() == inst->getContext()->Bool());

        bool bv = valArg->get<bool>();
        stringstream ss;
        ss << (bv ? "1" : "0");
        argStr = ss.str();
      }
    }

    assert(foundValue);

    return argStr;
  }

  string printConstant(Instance* inst, const vdisc vd, const NGraph& g) {
    if (getQualifiedOpName(*inst) == "corebit.const") {
      return printBitConstant(inst, vd, g);
    } else {
      return printBVConstant(inst, vd, g);
    }
  }

  string printOpThenMaskBinop(const WireNode& wd,
                              const vdisc vd,
                              const NGraph& g,
                              LayoutPolicy& lp) {
    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    string opString = getOpString(*inst);

    string compString =
      parens(printOpResultStr(arg1, g, lp) + opString + printOpResultStr(arg2, g, lp));

    // And not standard width
    if (isDASHR(*inst)) {
      uint tw = typeWidth(*(arg1.getWire()->getType()));
      uint containWidth = containerTypeWidth(*(arg1.getWire()->getType()));
      if (containWidth > tw) {

        string mask =
          parens(bitMaskString(printOpResultStr(arg2, g, lp)) + " << " + parens(to_string(tw) + " - " + printOpResultStr(arg2, g, lp)));

        string signBitSet =
          parens("0x01 & " + parens(printOpResultStr(arg1, g, lp) +  " >> " + parens(to_string(tw - 1))));

        compString = parens(ite(signBitSet, mask, "0") + " | " + parens(compString));
      }
    }

    // Check if this output needs a mask
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      res += maskResult(*(outPair.second->getType()), compString);
    } else {
      res += compString;
    }

    return res;
  }

  string castToSigned(Type& tp, const std::string& expr) {
    return parens(parens(signedCTypeString(tp)) + " " + expr);
  }

  string castToUnSigned(Type& tp, const std::string& expr) {
    return parens(parens(unSignedCTypeString(tp)) + " " + expr);
  }

  string seString(Type& tp, const std::string& arg) {


    uint startWidth = typeWidth(tp);
    uint extWidth = containerTypeWidth(tp);

    if (startWidth < extWidth) {
      return "SIGN_EXTEND( " + to_string(startWidth) + ", " +
        to_string(extWidth) + ", " +
        arg + " )";
    } else if (startWidth == extWidth) {
      return parens(arg);
    } else {
      cout << "ERROR: trying to sign extend from " << startWidth << " to " << extWidth << endl;
      assert(false);
    }

  }

  string
  printSEThenOpThenMaskBinop(Instance* inst,
                             const vdisc vd,
                             const NGraph& g,
                             LayoutPolicy& lp) {
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    string opString = getOpString(*inst);

    Type& arg1Tp = *((arg1.getWire())->getType());
    Type& arg2Tp = *((arg2.getWire())->getType());

    string rs1 = printOpResultStr(arg1, g, lp);
    string rs2 = printOpResultStr(arg2, g, lp);

    string opStr = castToSigned(arg1Tp, seString(arg1Tp, rs1)) +
      opString +
      castToSigned(arg2Tp, seString(arg2Tp, rs2));

    string res;
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      res += maskResult(*(outPair.second->getType()), opStr);
    } else {
      res += opStr;
    }
      
    return res;
  }

  bool isMux(Instance& inst) {
    string genRefName = getInstanceName(inst);
    return genRefName == "mux";
  }

  string printMux(Instance* inst, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    assert(isMux(*inst));

    auto ins = getInputConnections(vd, g);

    assert(ins.size() == 3);

    InstanceValue sel = findArg("sel", ins);
    InstanceValue i0 = findArg("in0", ins);
    InstanceValue i1 = findArg("in1", ins);
    
    return ite(printOpResultStr(sel, g, lp),
               printOpResultStr(i1, g, lp),
               printOpResultStr(i0, g, lp));
  }

  string printAddOrSubWithCIN(const WireNode& wd,
                              const vdisc vd,
                              const NGraph& g,
                              LayoutPolicy& lp) {
    auto ins = getInputs(vd, g);

    assert(ins.size() == 3);
    
    Instance* inst = toInstance(wd.getWire());
    auto outSelects = getOutputSelects(inst);

    assert((outSelects.size() == 1));

    string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    // Either it is a binop or there is a cin
    assert((inConns.size() == 2) || (inConns.size() == 3));

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);
    InstanceValue carry = findArg("cin", inConns);

    string opString = getOpString(*inst);

    string compString =
      parens(printOpResultStr(arg1, g, lp) + opString + printOpResultStr(arg2, g, lp) + " + " + printOpResultStr(carry, g, lp));

    // Check if this output needs a mask
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      res += maskResult(*(outPair.second->getType()), compString);
    } else {
      res += compString;
    }

    return res;

  }

  string checkSumOverflowStr(Type& tp,
                             const std::string& in0StrNC,
                             const std::string& in1StrNC) {
    string in0Str = castToUnSigned(tp, in0StrNC);
    string in1Str = castToUnSigned(tp, in0StrNC);

    string sumString = castToUnSigned(tp, parens(in0StrNC + " + " + in1StrNC));
    string test1 = parens(sumString + " < " + in0Str);
    string test2 = parens(sumString + " < " + in1Str);
    return parens(test1 + " || " + test2);
  }

  // NOTE: This function prints the full assignment of values
  string printAddOrSubCIN_COUT(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    auto ins = getInputs(vd, g);

    assert(ins.size() == 3);
    
    Instance* inst = toInstance(wd.getWire());
    auto outSelects = getOutputSelects(inst);

    assert((outSelects.size() == 2));

    Wireable* resultSelect = findSelect("out", outSelects);
    Wireable* coutSelect = findSelect("cout", outSelects);

    string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    // Either it is a binop or there is a cin
    assert((inConns.size() == 2) || (inConns.size() == 3));

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);
    InstanceValue carry = findArg("cin", inConns);

    string opString = getOpString(*inst);

    string in0Str = printOpResultStr(arg1, g, lp);
    string in1Str = printOpResultStr(arg2, g, lp);
    string carryStr = printOpResultStr(carry, g, lp);
    string sumStr = parens(in0Str + opString + in1Str);

    string compString =
      parens(sumStr + " + " + carryStr);

    Type& tp = *(resultSelect->getType());
    res += maskResult(tp, compString);

    // This does not actually handle the case where the underlying types are the
    // a fixed architecture width
    string carryRes;
    if (standardWidth(tp)) {
      string firstOverflow = checkSumOverflowStr(tp, in0Str, in1Str);
      string secondOverflow = checkSumOverflowStr(tp, sumStr, carryStr);
      carryRes = parens(firstOverflow + " || " + secondOverflow);
    } else {

      carryRes = parens(parens(compString + " >> " + to_string(typeWidth(tp))) + " & 0x1");

    }

    string carryString = cVar(*coutSelect) + " = " + carryRes;

    return ln(cVar(*resultSelect) + " = " + res) + ln(carryString);

  }

  // NOTE: This function prints the full assignment of values
  string printAddOrSubCOUT(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    auto ins = getInputs(vd, g);

    assert(ins.size() == 2);
    
    Instance* inst = toInstance(wd.getWire());
    auto outSelects = getOutputSelects(inst);

    assert((outSelects.size() == 2));

    Wireable* resultSelect = findSelect("out", outSelects);
    Wireable* coutSelect = findSelect("cout", outSelects);

    string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    // Either it is a binop or there is a cin
    assert((inConns.size() == 2) || (inConns.size() == 3));

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    string opString = getOpString(*inst);

    string in0Str = printOpResultStr(arg1, g, lp);
    string in1Str = printOpResultStr(arg2, g, lp);
    string sumStr = parens(in0Str + opString + in1Str);

    string compString = sumStr;

    Type& tp = *(resultSelect->getType());
    res += maskResult(tp, compString);

    // This does not actually handle the case where the underlying types are the
    // a fixed architecture width
    string carryRes;
    if (standardWidth(tp)) {
      string firstOverflow = checkSumOverflowStr(tp, in0Str, in1Str);
      carryRes = parens(firstOverflow);
    } else {

      carryRes = parens(parens(compString + " >> " + to_string(typeWidth(tp))) + " & 0x1");

    }

    string carryString = cVar(*coutSelect) + " = " + carryRes;

    return ln(cVar(*resultSelect) + " = " + res) + ln(carryString);

  }
  
  string printTernop(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    assert(getInputs(vd, g).size() == 3);

    Instance* inst = toInstance(wd.getWire());
    if (isMux(*inst)) {
      return printMux(inst, vd, g, lp);
    }

    if (isAddOrSub(*inst)) {
      // Add and subtract need special treatment because of cin and cout flags
      return printAddOrSubWithCIN(wd, vd, g, lp);
    }

    assert(false);
  }

  string printBinop(const WireNode& wd,
                    const vdisc vd,
                    const NGraph& g,
                    LayoutPolicy& lp) {

    assert(getInputs(vd, g).size() == 2);

    Instance* inst = toInstance(wd.getWire());

    if (isBitwiseOp(*inst) ||
        isSignInvariantOp(*inst) ||
        isUnsignedCmp(*inst) ||
        isShiftOp(*inst) ||
        isUDivOrRem(*inst)) {
      return printOpThenMaskBinop(wd, vd, g, lp);
    }

    if (isSignedCmp(*inst) ||
        isSDivOrRem(*inst)) {
      return printSEThenOpThenMaskBinop(inst, vd, g, lp);
    }

    cout << "Unsupported binop = " << inst->toString() << " from module = " << inst->getModuleRef()->getName() << endl;

    assert(false);
  }

  bool hasEnable(Wireable* w) {
    assert(isRegisterInstance(w));

    return recordTypeHasField("en", w->getType());
  }

  string enableRegReceiver(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* sl = toSelect((*(begin(outSel))).second);

    assert(isInstance(sl->getParent()));

    Instance* r = toInstance(sl->getParent());

    auto ins = getInputConnections(vd, g);

    assert((ins.size() == 3) || (ins.size() == 2 && !hasEnable(wd.getWire())));

    string s = lp.outputVarName(*wd.getWire()) + " = ";

    InstanceValue add = findArg("in", ins);

    string oldValName = lp.outputVarName(*r);

    // Need to handle the case where clock is not actually directly from an input
    // clock variable
    if (hasEnable(wd.getWire())) {
      string condition = "";
      
      InstanceValue en = findArg("en", ins);
      condition += printOpResultStr(en, g, lp);

      s += ite(parens(condition),
               printOpResultStr(add, g, lp),
               oldValName) + ";\n";
    } else {
      s += printOpResultStr(add, g, lp) + ";\n";
    }

    return s;
  }

  string printRegister(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    assert(wd.isSequential);

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* s = toSelect((*(begin(outSel))).second);

    assert(isInstance(s->getParent()));

    Instance* r = toInstance(s->getParent());
    if (!wd.isReceiver) {
      if (!lp.getReadRegsDirectly()) {
        return ln(cVar(*s) + " = " + lp.outputVarName(*r));
      } else {
        return "";
      }
    } else {
      return enableRegReceiver(wd, vd, g, lp);
    }
  }

  string opResultStr(const WireNode& wd,
                     const vdisc vd,
                     const NGraph& g,
                     LayoutPolicy& lp) {

    Instance* inst = toInstance(wd.getWire());
    auto ins = getInputs(vd, g);
    
    if (ins.size() == 3) {
      return printTernop(wd, vd, g, lp);
    }

    if (ins.size() == 2) {
      return printBinop(wd, vd, g, lp);
    }

    if (ins.size() == 1) {
      return printUnop(inst, vd, g, lp);
    }

    if (ins.size() == 0) {
      return printConstant(inst, vd, g);
    }

    cout << "Unsupported instance = " << inst->toString() << endl;
    assert(false);
    return "";
  }

  string printMemory(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    assert(wd.isSequential);

    auto outSel = getOutputSelects(wd.getWire());
    
    assert(outSel.size() == 1);
    Select* s = toSelect((*(begin(outSel))).second);
    
    assert(isInstance(s->getParent()));

    Instance* r = toInstance(s->getParent());

    auto ins = getInputConnections(vd, g);
    
    if (!wd.isReceiver) {
      assert(ins.size() == 1);

      InstanceValue raddr = findArg("raddr", ins);

      return ln(cVar(*s) + " = " +
                parens(lp.outputVarName(*r) +
                       "[ " + printOpResultStr(raddr, g, lp) + " ]"));

    } else {
      assert(ins.size() == 4);

      InstanceValue waddr = findArg("waddr", ins);
      InstanceValue wdata = findArg("wdata", ins);
      InstanceValue wen = findArg("wen", ins);

      string condition = printOpResultStr(wen, g, lp);

      string oldValueName = lp.outputVarName(*r) + "[ " + printOpResultStr(waddr, g, lp) + " ]";

      string s = oldValueName + " = ";
      s += ite(parens(condition),
               printOpResultStr(wdata, g, lp),
               oldValueName);

      return ln(s);
      
    }
  }

  string printInstance(const WireNode& wd,
                       const vdisc vd,
                       const NGraph& g,
                       LayoutPolicy& layoutPolicy) {

    Instance* inst = toInstance(wd.getWire());

    if (isRegisterInstance(inst)) {
      return printRegister(wd, vd, g, layoutPolicy);
    }

    if (isMemoryInstance(inst)) {
      return printMemory(wd, vd, g, layoutPolicy);
    }

    auto outSelects = getOutputSelects(inst);

    if (outSelects.size() == 1) {

      pair<string, Wireable*> outPair = *std::begin(outSelects);
      string res;
      if (!isThreadShared(vd, g)) {
        res = cVar(*(outPair.second));
      } else {
        res = layoutPolicy.outputVarName(*(outPair.second));
      }

    
      return ln(res + " = " + opResultStr(wd, vd, g, layoutPolicy));
    } else {
      assert(outSelects.size() == 2);
      assert(isAddOrSub(*inst));

      auto ins = getInputs(vd, g);

      if (ins.size() == 3) {
      
        return printAddOrSubCIN_COUT(wd, vd, g, layoutPolicy);
      } else {
        assert(ins.size() == 2);

        return printAddOrSubCOUT(wd, vd, g, layoutPolicy);
        
      }
    }
  }

  bool isCombinationalInstance(const WireNode& wd) {
    assert(isInstance(wd.getWire()));

    if (isRegisterInstance(wd.getWire())) {
      return false;
    }
    if (isMemoryInstance(wd.getWire())) {
      cout << "Found memory instance" << endl;
      return false;
    }

    return true;
  }

  string printOpResultStr(const InstanceValue& wd,
                          const NGraph& g,
                          LayoutPolicy& lp) {
    assert(isSelect(wd.getWire()));

    Wireable* sourceInstance = extractSource(toSelect(wd.getWire()));    
    if (isRegisterInstance(sourceInstance)) {

      if (lp.getReadRegsDirectly() == false) {
        return cVar(wd);
      } else {
        return lp.outputVarName(*sourceInstance);
      }
    }

    if (isMemoryInstance(sourceInstance)) {
      return cVar(wd);
    }

    // Is this the correct way to check if the value is an input?
    if (isSelect(sourceInstance) && fromSelf(toSelect(sourceInstance))) {
      return lp.outputVarName(wd);
    }

    if (isThreadShared(g.getOpNodeDisc(sourceInstance), g)) {
      return lp.outputVarName(wd);
    }
    assert(g.containsOpNode(sourceInstance));

    vdisc opNodeD = g.getOpNodeDisc(sourceInstance);

    // TODO: Should really check whether or not there is one connection using
    // the given variable, this is slightly too conservative
    if (g.getOutputConnections(opNodeD).size() == 1) {
      return opResultStr(combNode(sourceInstance), opNodeD, g, lp);
    }

    return "/* LOCAL */" + cVar(wd);
  }

  string printInternalVariables(const std::deque<vdisc>& topo_order,
                                NGraph& g,
                                Module&) {
    string str = "";
    for (auto& vd : topo_order) {
      WireNode wd = getNode( g, vd);
      Wireable* w = wd.getWire();

      for (auto inSel : getOutputSelects(w)) {
        Select* in = toSelect(inSel.second);

        if (!fromSelfInterface(in)) {
          if (!arrayAccess(in)) {

            if (!wd.isSequential) {

              str += cArrayTypeDecl(*(in->getType()), " " + cVar(*in)) + ";\n";


            } else {
              if (wd.isReceiver) {
                str += cArrayTypeDecl(*(in->getType()), " " + cVar(*in)) + ";\n";
              }
            }
          }
        }
      }
    }

    return str;
  }

  string printSimFunctionPrefix(const std::deque<vdisc>& topo_order,
                                NGraph& g,
                                Module& mod) {
    string str = "";

    // Declare all variables
    str += "\n// Variable declarations\n";

    str += "\n// Internal variables\n";
    str += printInternalVariables(topo_order, g, mod);

    return str;
  }

  vector<string>
  updateSequentialElements(const std::deque<vdisc>& topoOrder,
                           NGraph& g,
                           Module& mod,
                           const int threadNo,
                           LayoutPolicy& layoutPolicy) {
    vector<string> simLines;
    // Update stateful element values

    for (auto& vd : topoOrder) {

      WireNode wd = getNode(g, vd);

      Wireable* inst = wd.getWire();

      if (isInstance(inst)) { 
        if (!isCombinationalInstance(wd) &&
            wd.isReceiver) {

          simLines.push_back(printInstance(wd, vd, g, layoutPolicy));

        }
      }
    }

    return simLines;

  }

  vector<string>
  updateSequentialOutputs(const std::deque<vdisc>& topoOrder,
                          NGraph& g,
                          Module& mod,
                          const int threadNo,
                          LayoutPolicy& layoutPolicy) {

    vector<string> simLines;

    for (auto& vd : topoOrder) {

      WireNode wd = getNode(g, vd);
      Wireable* inst = wd.getWire();

      if (isInstance(inst)) { 

        if (!isCombinationalInstance(wd) &&
            !(wd.isReceiver)) {

          simLines.push_back(printInstance(wd, vd, g, layoutPolicy));

        }

      }

    }

    return simLines;
    
  }  

  vector<string>
  updateCombinationalLogic(const std::deque<vdisc>& topoOrder,
                           NGraph& g,
                           Module& mod,
                           const int threadNo,
                           LayoutPolicy& layoutPolicy) {
    vector<string> simLines;

    int i = 0;

    for (auto& vd : topoOrder) {

      string val = "<UNSET>";
      WireNode wd = getNode(g, vd);

        Wireable* inst = wd.getWire();

        if (isInstance(inst)) { 

          if ((isCombinationalInstance(wd)) &&
              ((g.getOutputConnections(vd).size() > 1) ||
               (isThreadShared(vd, g) && wd.getThreadNo() == threadNo))) {

            simLines.push_back(printInstance(wd, vd, g, layoutPolicy));

          }

        } else {

          if (inst->getType()->isInput()) {

            auto inConns = getInputConnections(vd, g);

            // If not an instance copy the input values
            for (auto inConn : inConns) {

              Wireable& outSel = *(inConn.second.getWire());
              string outVarName = layoutPolicy.outputVarName(outSel);

              simLines.push_back(ln(outVarName + " = " + printOpResultStr(inConn.first, g, layoutPolicy)));

            }

          }
        }

      if ((i % 500) == 0) {
        cout << "Code for instance " << i << " = " << val << endl;
      }
      i++;
    }


    return simLines;
  }

  struct CircuitPaths {
    deque<vdisc> threadNodes;
    vector<deque<vdisc> > preSequentialAlwaysDAGs;
    vector<deque<vdisc> > preSequentialDAGs;
    vector<deque<vdisc> > postSequentialDAGs;
    vector<deque<vdisc> > postSequentialAlwaysDAGs;
    vector<deque<vdisc> > pureCombDAGs;
  };

  CircuitPaths buildCircuitPaths(const std::deque<vdisc>& topoOrder,
                                 NGraph& g,
                                 Module& mod,
                                 const int threadNo) {
    CircuitPaths paths;

    for (auto& vd : topoOrder) {
      if (g.getNode(vd).getThreadNo() == threadNo) {
        paths.threadNodes.push_back(vd);
      }
    }

    vector<set<vdisc>> ccs =
      connectedComponentsIgnoringInputs(g);

    cout << "# of connected components = " << ccs.size() << endl;

    // Set presequential DAGs
    for (auto& cc : ccs) {
      deque<vdisc> nodes;
      for (auto& vd : paths.threadNodes) {
        if (elem(vd, cc)) {
          nodes.push_back(vd);
        }
      }

      if (subgraphHasCombinationalOutput(nodes, g) &&
          subgraphHasSequentialOutput(nodes, g)) {
        // Need to split up graphs of this form
        paths.preSequentialAlwaysDAGs.push_back(nodes);
      }

      if (subgraphHasCombinationalInput(nodes, g) &&
          subgraphHasSequentialInput(nodes, g)) {
        // Need to split up graphs of this form
        paths.postSequentialAlwaysDAGs.push_back(nodes);
      }

      if (subgraphHasAllSequentialOutputs(nodes, g)) {
        paths.preSequentialDAGs.push_back(nodes);
      }

      if (subgraphHasAllSequentialInputs(nodes, g)) {
        paths.postSequentialDAGs.push_back(nodes);
      }
      
      if (subgraphHasAllCombinationalInputs(nodes, g) &&
          subgraphHasAllCombinationalOutputs(nodes, g)) {
        paths.pureCombDAGs.push_back(nodes);
      }
    }
    

    return paths;
  }

  typedef std::deque<vdisc> SubDAG;

  vector<vector<SubDAG> >
  groupIdenticalSubDAGs(const vector<SubDAG>& dags, const int groupSize) {
    vector<vector<SubDAG> > groups;
    //for (auto& dag : dags) {
    int i;
    for (i = 0; i < dags.size(); i += groupSize) {
      if ((i + groupSize) > dags.size()) {
        break;
      }

      vector<SubDAG> sg;      
      for (int j = 0; j < groupSize; j++) {
        sg.push_back(dags[i + j]);
      }
      groups.push_back(sg);
    }

    if (i < dags.size()) {
      vector<SubDAG> sg;      
      for (; i < dags.size(); i++) {
        sg.push_back(dags[i]);
      }

      groups.push_back(sg);
    }

    return groups;
  }

  void addDAGCode(std::vector<std::deque<vdisc> >& dags,
                  NGraph& g,
                  Module& mod,
                  const int threadNo,
                  LayoutPolicy& layoutPolicy,
                  std::vector<std::string>& simLines) {

    bool allSeqOut = true;
    for (auto& dag : dags) {
      if (dag.size() != 2) {
        allSeqOut = false;
        break;
      }

      WireNode startWd = g.getNode(dag[0]);
      if (!startWd.isSequential) {
        allSeqOut = false;
        break;
      }

      WireNode endWd = g.getNode(dag[1]);
      if (!isGraphOutput(endWd)) {
        allSeqOut = false;
        break;
      }

    }

    if (!allSeqOut || (dags.size() < 8)) {
      for (auto& nodes : dags) {
        concat(simLines,
               updateSequentialOutputs(nodes, g, mod, threadNo, layoutPolicy));
        concat(simLines,
               updateCombinationalLogic(nodes, g, mod, threadNo, layoutPolicy));
      }
      return;
    }

    // Parallelizeable output graphs
    simLines.push_back("// ====== Vectorizing accesses ======\n");

    int opWidth = 16;
    int groupSize = 256 / opWidth;

    cout << "groupSize = " << groupSize << endl;
    vector<vector<SubDAG> > dagGroups = groupIdenticalSubDAGs(dags, groupSize);

    vector<vector<string> > state_var_groups;
    
    for (int i = 0; i < dagGroups.size(); i++) {
      vector<SubDAG>& group = dagGroups[i];

      // Create forced variable groups in layout
      vector<string> invars;
      vector<string> outvars;
      for (auto& dag : group) {
        string stateInLoc =
          cVar(*(g.getNode(dag[0]).getWire()));

        invars.push_back(stateInLoc);

        string stateOutLoc =
          cVar(*(g.getNode(dag[1]).getWire()));

        outvars.push_back(stateOutLoc);

      }

      state_var_groups.push_back(invars);
      state_var_groups.push_back(outvars);
      
      SubDAG init = group[0];
      string stateInLoc =
        layoutPolicy.outputVarName(*(g.getNode(init[0]).getWire()));
      string stateOutLoc =
        layoutPolicy.outputVarName(*(g.getNode(init[1]).getWire()));
      string tmp = cVar(*(g.getNode(init[0]).getWire()));

      simLines.push_back("__m256i " + tmp +
                         " = _mm256_loadu_si256((__m256i const*)" +
                         stateInLoc + ");\n");

      simLines.push_back("_mm256_storeu_si256((__m256i *)" + stateOutLoc +
                         ", " +
                         tmp + ");\n");

    }

    cout << "====== State var groups" << endl;
    for (auto& gp : state_var_groups) {
      cout << "--------- Group" << endl;
      for (auto& var : gp) {
        cout << "-- " << var << endl;
      }
    }

    for (auto& gp : state_var_groups) {
      layoutPolicy.forceAdjacent(gp);
    }
  }

  string printSimFunctionBody(const std::deque<vdisc>& topoOrder,
                              NGraph& g,
                              Module& mod,
                              LayoutPolicy& layoutPolicy) {

    int threadNo = 0;
    cout << "Printing sim function for " << threadNo << endl;

    string str = printSimFunctionPrefix(topoOrder, g, mod);

    // Print out operations in topological order
    str += "\n// Simulation code\n";

    vector<string> simLines;

    auto paths = buildCircuitPaths(topoOrder, g, mod, threadNo);

    auto clk = findMainClock(g);

    if (clk != nullptr) {
      InstanceValue clkInst(clk);
    
      string condition =
        parens(parens(layoutPolicy.lastClkVarName(clkInst) + " == 0") + " && " +
               parens(layoutPolicy.clkVarName(clkInst) + " == 1"));

      addDAGCode(paths.preSequentialAlwaysDAGs,
                 g, mod, threadNo, layoutPolicy, simLines);

      simLines.push_back("if " + condition + " {\n");
        
      // Only need to update the DAGS that start from an input, otherwise the
      // result is fresh already
      simLines.push_back("\n// ----- Update combinational logic before clock\n");
      addDAGCode(paths.preSequentialDAGs,
                 g, mod, threadNo, layoutPolicy, simLines);
      simLines.push_back("\n// ----- Done\n");

      simLines.push_back("\n// ----- Updating sequential logic\n");
      concat(simLines,
             updateSequentialElements(paths.threadNodes, g, mod, threadNo, layoutPolicy));
      simLines.push_back("\n// ----- Done\n");
      // No need to print out register updates
      layoutPolicy.setReadRegsDirectly(true);
      simLines.push_back("\n// ----- Update combinational logic after clock\n");

      cout << "# of post sequential dags = " << paths.postSequentialDAGs.size() << endl;
      for (auto& dag : paths.postSequentialDAGs) {
        cout << dag.size() << endl;
      }
      addDAGCode(paths.postSequentialDAGs,
                 g, mod, threadNo, layoutPolicy, simLines);
      simLines.push_back("\n// ----- Done\n");

      simLines.push_back("\n}\n");
      addDAGCode(paths.postSequentialAlwaysDAGs,
                 g, mod, threadNo, layoutPolicy, simLines);
      
    }

    simLines.push_back("\n// ----- Update pure combinational logic\n");
    addDAGCode(paths.pureCombDAGs,
               g, mod, threadNo, layoutPolicy, simLines);

    simLines.push_back("\n// ----- Done\n");
    
    cout << "Done writing sim lines, now need to concatenate them" << endl;

    for (auto& ln : simLines) {
      str += ln;
    }

    cout << "Done concatenating" << endl;

    return str;
  }

  string printDecl(const ModuleCode& mc) {
    string code = "";
    code += "#include <stdint.h>\n";
    code += "#include <cstdio>\n\n";
    code += "#include \"bit_vector.h\"\n\n";

    code += "using namespace bsim;\n\n";

    code += printEvalStruct(mc);

    code += "void simulate( circuit_state* state );\n";

    return code;
  }

  std::string printCode(const ModuleCode& mc) {
    return mc.codeString;
  }

  ModuleCode buildCode(const std::deque<vdisc>& topoOrder,
                       NGraph& g,
                       CoreIR::Module* mod,
                       const std::string& baseName) {

    string code = "";

    code += "#include \"" + baseName + "\"\n";
    code += "#include <immintrin.h>\n";
    code += "using namespace bsim;\n\n";

    code += seMacroDef();
    code += maskMacroDef();

    CustomStructLayout sl(mod->getDef()->getContext());

    code += "void simulate_0( circuit_state* state ) {\n";
    code += printSimFunctionBody(topoOrder, g, *mod, sl);
    code += "}\n\n";

    code += "void simulate( circuit_state* state ) {\n";
    code += ln("simulate_0( state )");
    code += "}\n";

    ModuleCode mc(g, mod);
    mc.codeString = code;
    mc.structLayout = sl.varDecls;

    return mc;
  }

}
