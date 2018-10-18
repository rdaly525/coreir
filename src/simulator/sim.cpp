#include "coreir/simulator/simulator.h"

#include "coreir/passes/transform/flatten.h"
#include "coreir/passes/transform/rungenerators.h"

#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/dag_optimization.h"
#include "coreir/simulator/low_rep.h"
#include "coreir/simulator/print_c.h"
#include "coreir/simulator/utils.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  std::vector<std::string> printSIMDNode(const vdisc vd,
                                         const int opWidth,
                                         NGraph& g,
                                         Module& mod,
                                         LayoutPolicy& lp);

  LowExpr* printBinop(const WireNode& wd,
                      const vdisc vd,
                      const NGraph& g,
                      LayoutPolicy& lp);

  LowExpr* printOpResultStr(const InstanceValue& wd,
                            const NGraph& g,
                            LayoutPolicy& lp);

  LowExpr* opResultStr(const WireNode& wd,
                       const vdisc vd,
                       const NGraph& g,
                       LayoutPolicy& lp);

  LowExpr* bitMaskExpression(LowExpr* exp) {
    return new LowBinop("-",
                        new LowBinop("<<",
                                     new LowId("1ULL"),
                                     exp),
                        new LowBitVec(BitVec(64, 1)));
  }
  
  LowExpr* bitMaskExpression(uint w) {
    assert(w > 0);

    return new LowBinop("-",
                        new LowBinop("<<",
                                     new LowId("1ULL"),
                                     new LowBitVec(BitVec(64, w))),
                        new LowBitVec(BitVec(64, 1)));
  }
  
  LowExpr* maskResultExpr(const uint w, LowExpr* const expr) {
    return new LowBinop("MASK", new LowBitVec(BitVec(32, w)), expr);
  }

  LowExpr* maskResultExpression(CoreIR::Type& tp, LowExpr* const expr) {
    if (standardWidth(tp)) {
      return expr;
    }

    return maskResultExpr(typeWidth(tp), expr);
  }

  std::pair<std::string, Wireable*> getOutSelect(Instance* const inst) {
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    return outPair;
  }

  LowExpr* printUnop(Instance* inst,
                     const vdisc vd,
                     const NGraph& g,
                     LayoutPolicy& lp) {
    auto outPair = getOutSelect(inst);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 1);

    Conn cn = (*std::begin(inConns));

    Wireable* dest = inConns[0].second.getWire();
    assert(isSelect(dest));

    Select* destSel = toSelect(dest);
    if (!(destSel->getParent() == inst)) {
      cout << "Destination select: " << destSel->toString() << endl;
    }
    assert(destSel->getParent() == inst);

    string opString = getOpString(*inst);

    LowExpr* val = nullptr;
    if (opString != "andr") {
      val = new LowUnop(opString, printOpResultStr(cn.first, g, lp));
    } else {

      uint w = typeWidth(*(cn.first.getWire()->getType()));
      val = new LowBinop("==",
                         printOpResultStr(cn.first, g, lp),
                         bitMaskExpression(w));

    }

    return maskResultExpression(*((outPair.second)->getType()), val);
  }

  LowExpr* printBVConstant(Instance* inst, const vdisc vd, const NGraph& g) {
    for (auto& arg : inst->getModArgs()) {
      if (arg.first == "value") {

        Value* valArg = arg.second;

        cout << "Value type = " << valArg->getValueType()->toString() << endl;

        BitVector bv = valArg->get<BitVector>();
        return new LowBitVec(bv);

      }
    }

    ASSERT(false,"did not find 'value' in modargs of " + toString(inst));
  }

  LowExpr* printBitConstant(Instance* inst, const vdisc vd, const NGraph& g) {

    for (auto& arg : inst->getModArgs()) {
      if (arg.first == "value") {

        Value* valArg = arg.second;

        assert(valArg->getValueType() == inst->getContext()->Bool());

        bool bv = valArg->get<bool>();

        if (bv == true) {
          return new LowBitVec(BitVec(1, 1));
        } else {
          return new LowBitVec(BitVec(1, 0));
        }
      }
    }

    assert(false);

  }

  LowExpr* printConstant(Instance* inst, const vdisc vd, const NGraph& g) {
    if (getQualifiedOpName(*inst) == "corebit.const") {
      return printBitConstant(inst, vd, g);
    } else {
      return printBVConstant(inst, vd, g);
    }
  }


  LowExpr* castToSigned(Type& tp, LowExpr* const expr) {
    return new LowId(parens(parens(signedCTypeString(tp)) + " " + expr->cString()));
  }

  LowExpr* castToUnSigned(Type& tp, LowExpr* const expr) {
    return new LowId(parens(parens(unSignedCTypeString(tp)) + " " + expr->cString()));
  }
  
  LowExpr* printOpThenMaskBinop(const WireNode& wd,
                                const vdisc vd,
                                const NGraph& g,
                                LayoutPolicy& lp) {
    Instance* inst = toInstance(wd.getWire());

    pair<string, Wireable*> outPair = getOutSelect(inst);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    string opString = getOpString(*inst);

    LowExpr* expr = new LowBinop(opString,
                                 printOpResultStr(arg1, g, lp),
                                 printOpResultStr(arg2, g, lp));

    // And not standard width
    if (isDASHR(*inst)) {
      uint tw = typeWidth(*(arg1.getWire()->getType()));

        LowExpr* maskExpr =
          new LowBinop("<<",
                       bitMaskExpression(printOpResultStr(arg2, g, lp)),
                       new LowBinop("-",
                                    new LowId(to_string(tw)),
                                    printOpResultStr(arg2, g, lp)));

        string mask = maskExpr->cString();

        LowExpr* signBitSet =
          new LowBinop("&",
                       new LowBitVec(BitVec(1, 1)),
                       new LowBinop(">>",
                                    printOpResultStr(arg1, g, lp),
                                    new LowId(to_string(tw - 1))));

        expr =
          new LowBinop("|",
                       new LowId(ite(signBitSet->cString(), mask, "0")),
                       expr);
    }

    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      expr = maskResultExpression(*(outPair.second->getType()), expr);
    }

    return castToUnSigned(*(outPair.second->getType()), expr);
  }

  LowExpr* seString(Type& tp, LowExpr* const arg) {
    uint startWidth = typeWidth(tp);
    uint extWidth = containerTypeWidth(tp);

    if (startWidth < extWidth) {
      return new LowId("SIGN_EXTEND( " + to_string(startWidth) + ", " +
                       to_string(extWidth) + ", " +
                       arg->cString() + " )");
    } else if (startWidth == extWidth) {
      return arg;
    } else {
      cout << "ERROR: trying to sign extend from " << startWidth << " to " << extWidth << endl;
      assert(false);
    }

  }

  LowExpr*
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

    LowExpr* rs1 = printOpResultStr(arg1, g, lp);
    LowExpr* rs2 = printOpResultStr(arg2, g, lp);

    LowExpr* opStr =
      new LowBinop(opString,
                   castToSigned(arg1Tp, seString(arg1Tp, rs1)),
                   castToSigned(arg2Tp, seString(arg2Tp, rs2)));

    LowExpr* res;
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      res = maskResultExpression(*(outPair.second->getType()), opStr);
    } else {
      res = opStr;
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
    
    return ite(printOpResultStr(sel, g, lp)->cString(),
               printOpResultStr(i1, g, lp)->cString(),
               printOpResultStr(i0, g, lp)->cString());
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
      parens(printOpResultStr(arg1, g, lp)->cString() + opString + printOpResultStr(arg2, g, lp)->cString() + " + " + printOpResultStr(carry, g, lp)->cString());

    // Check if this output needs a mask
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      res += maskResult(*(outPair.second->getType()), compString);
    } else {
      res += compString;
    }

    return res;

  }

  LowExpr* checkSumOverflowStr(Type& tp,
                               LowExpr* const in0StrNC,
                               LowExpr* const in1StrNC) {

                             // const std::string& in0StrNC,
                             // const std::string& in1StrNC) {
    LowExpr* in0Str = castToUnSigned(tp, in0StrNC);
    LowExpr* in1Str = castToUnSigned(tp, in1StrNC);

    LowExpr* sumString = castToUnSigned(tp, new LowId(parens(in0StrNC->cString() + " + " + in1StrNC->cString())));
    string test1 = parens(sumString->cString() + " < " + in0Str->cString());
    string test2 = parens(sumString->cString() + " < " + in1Str->cString());
    return new LowId(parens(test1 + " || " + test2));
  }

  // NOTE: This function prints the full assignment of values
  void printAddOrSubCIN_COUT(const WireNode& wd,
                             const vdisc vd,
                             const NGraph& g,
                             LayoutPolicy& lp,
                             LowProgram& prog) {
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

    auto in0Str = printOpResultStr(arg1, g, lp);
    auto in1Str = printOpResultStr(arg2, g, lp);
    auto carryStr = printOpResultStr(carry, g, lp);
    auto sumStr = new LowBinop(opString, in0Str, in1Str); //parens(in0Str + opString + in1Str);

    string compString =
      parens(sumStr->cString() + " + " + carryStr->cString());

    Type& tp = *(resultSelect->getType());
    res += maskResult(tp, compString);

    // This does not actually handle the case where the underlying types are the
    // a fixed architecture width
    string carryRes;
    if (standardWidth(tp)) {
      auto firstOverflow = checkSumOverflowStr(tp, in0Str, in1Str);
      auto secondOverflow = checkSumOverflowStr(tp, sumStr, carryStr);
      carryRes = parens(firstOverflow->cString() + " || " + secondOverflow->cString());
    } else {

      carryRes = parens(parens(compString + " >> " + to_string(typeWidth(tp))) + " & 0x1");

    }

    prog.addAssignStmt(new LowId(cVar(*resultSelect)),
                       new LowId(res));

    prog.addAssignStmt(new LowId(cVar(*coutSelect)),
                       new LowId(carryRes));
  }

  // NOTE: This function prints the full assignment of values
  void printAddOrSubCOUT(const WireNode& wd,
                         const vdisc vd,
                         const NGraph& g,
                         LayoutPolicy& lp,
                         LowProgram& prog) {
    auto ins = getInputs(vd, g);

    assert(ins.size() == 2);
    
    Instance* inst = toInstance(wd.getWire());
    auto outSelects = getOutputSelects(inst);

    assert((outSelects.size() == 2));

    Wireable* resultSelect = findSelect("out", outSelects);
    Wireable* coutSelect = findSelect("cout", outSelects);

    //string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    // Either it is a binop or there is a cin
    assert((inConns.size() == 2) || (inConns.size() == 3));

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    string opString = getOpString(*inst);

    auto in0Str = printOpResultStr(arg1, g, lp);
    auto in1Str = printOpResultStr(arg2, g, lp);
    LowExpr* sumStr = new LowBinop(opString,
                                   in0Str,
                                   in1Str);

    auto compString = sumStr;

    Type& tp = *(resultSelect->getType());
    LowExpr* res = maskResultExpression(tp, compString);

    // This does not actually handle the case where the underlying types are the
    // a fixed architecture width
    string carryRes;
    if (standardWidth(tp)) {
      LowExpr* firstOverflow = checkSumOverflowStr(tp, in0Str, in1Str);
      carryRes = parens(firstOverflow->cString());
    } else {

      carryRes = parens(parens(compString->cString() + " >> " + to_string(typeWidth(tp))) + " & 0x1");

    }

    prog.addAssignStmt(new LowId(cVar(*resultSelect)), res);

    prog.addAssignStmt(new LowId(cVar(*coutSelect)),
                       new LowId(carryRes));

  }
  
  LowExpr* printTernop(const WireNode& wd, const vdisc vd, const NGraph& g, LayoutPolicy& lp) {
    assert(getInputs(vd, g).size() == 3);

    Instance* inst = toInstance(wd.getWire());
    if (isMux(*inst)) {
      return new LowId(printMux(inst, vd, g, lp));
    }

    if (isAddOrSub(*inst)) {
      // Add and subtract need special treatment because of cin and cout flags
      return new LowId(printAddOrSubWithCIN(wd, vd, g, lp));
    }

    ASSERT(false,toString(inst));
  }

  LowExpr* printBinop(const WireNode& wd,
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

  void enableRegReceiver(const WireNode& wd,
                         const vdisc vd,
                         const NGraph& g,
                         LayoutPolicy& lp,
                         LowProgram& prog) {

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* sl = toSelect((*(begin(outSel))).second);

    assert(isInstance(sl->getParent()));

    Instance* r = toInstance(sl->getParent());

    auto ins = getInputConnections(vd, g);

    assert((ins.size() == 3) || (ins.size() == 2 && !hasEnable(wd.getWire())));

    string resName = lp.outputVarName(*wd.getWire());

    InstanceValue add = findArg("in", ins);

    string oldValName = lp.outputVarName(*r);

    // Need to handle the case where clock is not actually directly from an input
    // clock variable
    string resStr;
    if (hasEnable(wd.getWire())) {
      LowExpr* condition;
      
      InstanceValue en = findArg("en", ins);
      condition = printOpResultStr(en, g, lp);

      resStr = ite(parens(condition->cString()),
                   printOpResultStr(add, g, lp)->cString(),
                   oldValName);
    } else {
      resStr = printOpResultStr(add, g, lp)->cString();
    }

    prog.addAssignStmt(new LowId(resName),
                       new LowId(resStr));

  }

  void printRegister(const WireNode& wd,
                     const vdisc vd,
                     const NGraph& g,
                     LayoutPolicy& lp,
                     LowProgram& prog) {
    assert(wd.isSequential);

    auto outSel = getOutputSelects(wd.getWire());

    if (outSel.size() == 0) {
      // Node has no outputs
      return;
    }

    if ((outSel.size() != 1)) {
      cout << "Register " << nodeString(wd) << " has " << outSel.size() << " out selects!" << endl;
      for (auto& outSel : getOutputSelects(wd.getWire())) {
        cout << outSel.first << " --> " << outSel.second->toString() << endl;
      }
      assert(false);
    }

    Select* s = toSelect((*(begin(outSel))).second);

    assert(isInstance(s->getParent()));

    Instance* r = toInstance(s->getParent());

    if (!wd.isReceiver) {
      if (!lp.getReadRegsDirectly()) {

        prog.addAssignStmt(new LowId(cVar(*s)),
                           new LowId(lp.outputVarName(*r)));

      } else {
        return;// "";
      }
    } else {
      enableRegReceiver(wd, vd, g, lp, prog);
    }

  }

  LowExpr* opResultStr(const WireNode& wd,
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
    return nullptr;
  }

  void printMemory(const WireNode& wd,
                     const vdisc vd,
                     const NGraph& g,
                   LayoutPolicy& lp,
                   LowProgram& prog) {
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

      prog.addAssignStmt(new LowId(cVar(*s)),
                         new LowId(parens(lp.outputVarName(*r) +
                                          "[ " + printOpResultStr(raddr, g, lp)->cString() + " ]")));

    } else {
      assert(ins.size() == 4);

      InstanceValue waddr = findArg("waddr", ins);
      InstanceValue wdata = findArg("wdata", ins);
      InstanceValue wen = findArg("wen", ins);

      string condition = printOpResultStr(wen, g, lp)->cString();

      string oldValueName = lp.outputVarName(*r) + "[ " + printOpResultStr(waddr, g, lp)->cString() + " ]";

      prog.addAssignStmt(new LowId(oldValueName),
                         new LowId(ite(parens(condition),
                                       printOpResultStr(wdata, g, lp)->cString(),
                                       oldValueName)));

    }
  }

  void printInstance(const WireNode& wd,
                     const vdisc vd,
                     const NGraph& g,
                     LayoutPolicy& layoutPolicy,
                     LowProgram& prog) {

    Instance* inst = toInstance(wd.getWire());

    if (isRegisterInstance(inst)) {
      printRegister(wd, vd, g, layoutPolicy, prog);
    } else if (isMemoryInstance(inst)) {
      printMemory(wd, vd, g, layoutPolicy, prog);
    } else {

      auto outSelects = getOutputSelects(inst);

      if (outSelects.size() == 1) {

        pair<string, Wireable*> outPair = *std::begin(outSelects);
        string res;
        if (!isThreadShared(vd, g)) {
          res = cVar(*(outPair.second));
        } else {
          res = layoutPolicy.outputVarName(*(outPair.second));
        }

        prog.addAssignStmt(new LowId(res),
                           opResultStr(wd, vd, g, layoutPolicy));

      } else {
        assert(outSelects.size() == 2);
        ASSERT(isAddOrSub(*inst),"This instance with 2+ output ports is undefined: " + inst->getModuleRef()->toString());

        auto ins = getInputs(vd, g);

        if (ins.size() == 3) {

          printAddOrSubCIN_COUT(wd, vd, g, layoutPolicy, prog);

        } else {
          assert(ins.size() == 2);

          printAddOrSubCOUT(wd, vd, g, layoutPolicy, prog);
        }
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

  LowExpr* printOpResultStr(const InstanceValue& wd,
                            const NGraph& g,
                            LayoutPolicy& lp) {
    assert(isSelect(wd.getWire()));

    Wireable* sourceInstance = extractSource(toSelect(wd.getWire()));
    if (isRegisterInstance(sourceInstance)) {

      if (lp.getReadRegsDirectly() == false) {
        return new LowId(cVar(wd));
      } else {
        return new LowId(lp.outputVarName(*sourceInstance));
      }
    }

    if (isMemoryInstance(sourceInstance)) {
      return new LowId(cVar(wd));
    }

    // Is this the correct way to check if the value is an input?
    if (isSelect(sourceInstance) && fromSelf(toSelect(sourceInstance))) {
      return new LowId(lp.outputVarName(wd));
    }

    // TODO: Eliminate thread sharing analysis
    if (isThreadShared(g.getOpNodeDisc(sourceInstance), g)) {
      return new LowId(lp.outputVarName(wd));
    }
    assert(g.containsOpNode(sourceInstance));

    vdisc opNodeD = g.getOpNodeDisc(sourceInstance);

    // TODO: Should really check whether or not there is one connection using
    // the given variable, this is slightly too conservative
    if ((g.getOutputConnections(opNodeD).size() == 1) ||
        (isConstant(g.getNode(opNodeD)))) {

      return opResultStr(combNode(sourceInstance), opNodeD, g, lp);
    }

    return new LowId(cVar(wd));
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

  void
  updateSequentialElements(const SIMDGroup& group,
                           NGraph& g,
                           Module& mod,
                           LayoutPolicy& layoutPolicy,
                           LowProgram& prog) {

    auto topoOrder = group.nodes[0];
    
    if (group.nodes.size() == 1) {

      for (auto& vd : topoOrder) {
        WireNode wd = getNode(g, vd);
        Wireable* inst = wd.getWire();
        if (isInstance(inst)) { 
          if (!isCombinationalInstance(wd) &&
              wd.isReceiver) {

            printInstance(wd, vd, g, layoutPolicy, prog);

          }
        }
      }
    } else {

      assert(false);
      
    }

  }

  void
  updateCombinationalLogic(const std::deque<vdisc>& topoOrder,
                           NGraph& g,
                           Module& mod,
                           LayoutPolicy& layoutPolicy,
                           LowProgram& prog) {
    vector<string> simLines;

    int i = 0;

    for (auto& vd : topoOrder) {

      string val = "<UNSET>";
      WireNode wd = getNode(g, vd);

        Wireable* inst = wd.getWire();

        if (isInstance(inst)) { 

          if (((isCombinationalInstance(wd)) &&
               ((g.getOutputConnections(vd).size() > 1))) ||

              (!isCombinationalInstance(wd) &&
               !wd.isReceiver)) {

            printInstance(wd, vd, g, layoutPolicy, prog);
          }

        } else {

          if (inst->getType()->isInput()) {

            auto inConns = getInputConnections(vd, g);

            // If not an instance copy the input values
            for (auto inConn : inConns) {

              Wireable& outSel = *(inConn.second.getWire());
              string outVarName = layoutPolicy.outputVarName(outSel);

              prog.addAssignStmt(new LowId(outVarName),
                                 printOpResultStr(inConn.first, g, layoutPolicy));

            }

          }
        }

      if ((i % 500) == 0) {
        cout << "Code for instance " << i << " = " << val << endl;
      }
      i++;
    }

  }

  void addScalarDAGCode(const std::vector<std::deque<vdisc> >& dags,
                        NGraph& g,
                        Module& mod,
                        LayoutPolicy& layoutPolicy,
                        LowProgram& prog) {
    for (auto& nodes : dags) {
      updateCombinationalLogic(nodes,
                               g,
                               mod,
                               layoutPolicy,
                               prog);
    }
    return;
  }

  std::vector<std::string> printSIMDNode(const vdisc vd,
                                         const int opWidth,
                                         NGraph& g,
                                         Module& mod,
                                         LayoutPolicy& lp) {
    vector<string> simLines;
    if (isGraphInput(g.getNode(vd))) {
      string stateInLoc =
        lp.outputVarName(*(g.getNode(vd).getWire()));

      simLines.push_back("__m128i " + cVar(*(g.getNode(vd).getWire())) +
                         " = _mm_loadu_si128((__m128i const*) &" +
                         stateInLoc + ");\n");

      return simLines;
    } else if (isGraphOutput(g.getNode(vd))) {

      string stateOutLoc =
        lp.outputVarName(*(g.getNode(vd).getWire()));
        
      auto ins = getInputConnections(vd, g);

      cout << "Inputs to " << g.getNode(vd).getWire()->toString() << endl;
      for (auto& in : ins) {
        cout << in.first.getWire()->toString() << endl;
        cout << in.second.getWire()->toString() << endl;
      }

      assert(ins.size() == 1);

      InstanceValue resV = ins[0].first;
      // InstanceValue resV = findArg("in", ins);
      string res = cVar(resV.getWire());
        
      simLines.push_back("_mm_storeu_si128((__m128i *) &" + stateOutLoc +
                         ", " +
                         res + ");\n");

      return simLines;
    } else {

      Instance* inst = toInstance(g.getNode(vd).getWire());

      if (isRegisterInstance(inst)) {
        if (g.getNode(vd).isReceiver) {

          string stateOutLoc =
            lp.outputVarName(*(g.getNode(vd).getWire()));

          auto ins = getInputConnections(vd, g);
          InstanceValue resV = findArg("in", ins);
          string res = cVar(resV.getWire());
          simLines.push_back("_mm_storeu_si128((__m128i *) &" + stateOutLoc +
                             ", " +
                             res + ");\n");

        } else {
          string stateInLoc =
            lp.outputVarName(*(g.getNode(vd).getWire()));

          simLines.push_back("__m128i " + cVar(g.getNode(vd).getWire()->sel("out")) +
                             " = _mm_loadu_si128((__m128i const*) &" +
                             stateInLoc + ");\n");
            
        }

      } else if (getQualifiedOpName(*inst) == "coreir.and") {

        auto ins = getInputConnections(vd, g);
        string arg0 = cVar(findArg("in0", ins).getWire());
        string arg1 = cVar(findArg("in1", ins).getWire());

        string resName = cVar(*g.getNode(vd).getWire()->sel("out"));
          
        simLines.push_back(ln("__m128i " + resName + " = _mm_and_si128(" + arg0 + ", " + arg1 + ")"));
          
      } else if (getQualifiedOpName(*inst) == "coreir.or") {

        auto ins = getInputConnections(vd, g);
        string arg0 = cVar(findArg("in0", ins).getWire());
        string arg1 = cVar(findArg("in1", ins).getWire());

        string resName = cVar(*g.getNode(vd).getWire()->sel("out"));
          
        simLines.push_back(ln("__m128i " + resName + " = _mm_or_si128(" + arg0 + ", " + arg1 + ")"));
          
      } else {
        simLines.push_back("// NO CODE FOR: " + g.getNode(vd).getWire()->toString() + "\n");
      }

      return simLines;
    }

    cout << "Cannot print node " << g.getNode(vd).getWire()->toString() << endl;
    assert(false);
  }
  
  //std::vector<std::string>
  void
  printSIMDGroup(const SIMDGroup& group,
                 NGraph& g,
                 Module& mod,
                 LayoutPolicy& lp,
                 LowProgram& prog) {
    // If the group actually is scalar code just call the scalar printout
    if (group.nodes.size() == 1) {
      //LowProgram prog;
      addScalarDAGCode({group.nodes[0]}, g, mod, lp, prog);
      //return {prog.cString()};
      return;
    }

    assert(false);

  }

  void addDAGCode(const std::vector<SIMDGroup>& dags,
                  NGraph& g,
                  Module& mod,
                  LayoutPolicy& layoutPolicy,
                  LowProgram& prog) {

    for (auto& simdGroup : dags) {
      printSIMDGroup(simdGroup, g, mod, layoutPolicy, prog);
    }

  }

  enum GroupType {
    CODE_GROUP_PRE_CLK,
    CODE_GROUP_CLK,
    CODE_GROUP_POST_CLK,
  };

  struct CodeGroup {
    std::vector<SIMDGroup> dags;
    bool sequentialUpdate;
    GroupType tp;
  };

  void addDAGCode(const CodeGroup& code,
                  NGraph& g,
                  Module& mod,
                  LayoutPolicy& layoutPolicy,
                  LowProgram& prog) {

    if (!code.sequentialUpdate) {

      addDAGCode(code.dags, g, mod, layoutPolicy, prog);

    } else {
      for (auto& dag : code.dags) {

        updateSequentialElements(dag, g, mod, layoutPolicy, prog);

      }
    }
  }

  bool outToIn(const CodeGroup& gp,
               const CodeGroup& op,
               const NGraph& g) {
    if ((gp.dags.size() != 1) || (op.dags.size() != 1)) {
      return true;
    }

    SIMDGroup gp0 = gp.dags[0];
    SIMDGroup op0 = op.dags[0];

    if ((gp0.nodes.size() != 1) || (op0.nodes.size() != 1)) {
      return true;
    }

    SubDAG gpd = gp0.nodes[0];
    SubDAG opd = op0.nodes[0];

    set<Wireable*> outs;
    for (auto& vd : gpd) {
      if (isSubgraphOutput(vd, gpd, g)) {
        outs.insert(g.getNode(vd).getWire());
      }
    }
    set<Wireable*> ins;
    for (auto& vd : opd) {
      if (isSubgraphInput(vd, opd, g)) {
        ins.insert(g.getNode(vd).getWire());
      }
    }

    if (intersection(outs, ins).size() == 0) {
      return false;
    }

    return true;
    
  }

  string printSimFunctionBody(const std::deque<vdisc>& topoOrder,
                              NGraph& g,
                              Module& mod,
                              LayoutPolicy& layoutPolicy) {

    string str = printSimFunctionPrefix(topoOrder, g, mod);

    // Print out operations in topological order
    str += "\n// Simulation code\n";

    vector<string> simLines;

    auto paths = buildCircuitPaths(topoOrder, g, mod);

    auto clk = findMainClock(g);

    paths.preSequentialDAGs =
      pruneOutputs(paths.preSequentialDAGs, g);

    paths.postSequentialDAGs =
      pruneSequentialSinks(paths.postSequentialDAGs, g);
    
    if (clk != nullptr) {
      InstanceValue clkInst(clk);

      string condition =
        parens(parens(layoutPolicy.lastClkVarName(clkInst) + " == 0") + " && " +
               parens(layoutPolicy.clkVarName(clkInst) + " == 1"));

      LowProgram aProg;
      addDAGCode({paths.preSequentialAlwaysDAGs, false},
                 g, mod, layoutPolicy, aProg);
      simLines.push_back(aProg.cString());

      simLines.push_back("if " + condition + " {\n");

      if ((paths.postSequentialAlwaysDAGs.size() == 0) &&
          (paths.postSequentialAlwaysDAGs.size() == 0)) {
        cout << "All updates inside the clock!" << endl;
        simLines.push_back("// All updates inside clock\n");

        DirectedGraph<CodeGroup, CodeGroup*> updateOrder;

        vector<CodeGroup> codeGroups;
        cout << "# of pre updates  = " << paths.preSequentialDAGs.size() << endl;
        for (auto& gp : paths.preSequentialDAGs) {
          updateOrder.addVertex({{gp}, false, CODE_GROUP_PRE_CLK});
          updateOrder.addVertex({{gp}, true, CODE_GROUP_CLK});
        }

        cout << "# of post updates = " << paths.postSequentialDAGs.size() << endl;
        for (auto& gp : paths.postSequentialDAGs) {
          updateOrder.addVertex({{gp}, true, CODE_GROUP_CLK});
          updateOrder.addVertex({{gp}, false, CODE_GROUP_POST_CLK});
        }

        // Insert use to update edges
        for (auto& vd : updateOrder.getVerts()) {
          CodeGroup gp = updateOrder.getNode(vd);
          if (gp.tp == CODE_GROUP_PRE_CLK) {
            for (auto& ud : updateOrder.getVerts()) {
              CodeGroup op = updateOrder.getNode(ud);
              if (op.tp == CODE_GROUP_CLK) {

                // TODO: Check that the pre group contains an output that
                // is udpated in clock group
                updateOrder.addEdge(vd, ud);
              }
            }
          }
        }

        // Insert update to use edges
        for (auto& vd : updateOrder.getVerts()) {
          CodeGroup gp = updateOrder.getNode(vd);
          if (gp.tp == CODE_GROUP_CLK) {
            for (auto& ud : updateOrder.getVerts()) {
              CodeGroup op = updateOrder.getNode(ud);
              if (op.tp == CODE_GROUP_POST_CLK) {

                // TODO: Check that the post group contains an input that
                // is udpated in clock group
                if (outToIn(gp, op, g)) {
                  updateOrder.addEdge(vd, ud);
                }
              }
            }
          }
        }
        
        LowProgram clkProg;
        for (auto& group : topologicalSort(updateOrder)) {
          addDAGCode(updateOrder.getNode(group), g, mod, layoutPolicy, clkProg);
        }
        simLines.push_back(clkProg.cString());
        
      } else {

        vector<CodeGroup> codeGroups;

        codeGroups.push_back({paths.preSequentialDAGs, false});

        vector<SIMDGroup> allUpdates;
        concat(allUpdates, paths.postSequentialAlwaysDAGs);
        concat(allUpdates, paths.preSequentialAlwaysDAGs);

        concat(allUpdates, paths.postSequentialDAGs);
        concat(allUpdates, paths.preSequentialDAGs);
      
        allUpdates = deleteDuplicates(allUpdates);

        codeGroups.push_back({allUpdates, true});

        codeGroups.push_back({paths.postSequentialDAGs, false});

        LowProgram clkProg;
        for (auto& group : codeGroups) {
          addDAGCode(group, g, mod, layoutPolicy, clkProg);
        }
        simLines.push_back(clkProg.cString());
      }
      simLines.push_back("\n}\n");

      LowProgram postProg;
      addDAGCode({paths.postSequentialAlwaysDAGs, false},
                 g, mod, layoutPolicy, postProg);
      simLines.push_back(postProg.cString());
      
    }

    simLines.push_back("\n// ----- Update pure combinational logic\n");

    LowProgram combProg;
    addDAGCode({paths.pureCombDAGs, false},
               g, mod, layoutPolicy, combProg);
    simLines.push_back(combProg.cString());

    
    simLines.push_back("\n// ----- Done\n");

    if (clk != nullptr) {
      InstanceValue clkV(clk);
      string lastClkName = layoutPolicy.lastClkVarName(clkV);
      string clkName = layoutPolicy.clkVarName(clkV);

      simLines.push_back("\n// ----- Setting last clock values\n");
      LowAssign* clkUpdate = new LowAssign(new LowId(lastClkName),
                                           new LowId(clkName));
      simLines.push_back(clkUpdate->cString());

      delete clkUpdate;
    }
    
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

    code += "void simulate( circuit_state* __restrict const state );\n";

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

    code += "void simulate_0( circuit_state* __restrict const state ) {\n";
    code += printSimFunctionBody(topoOrder, g, *mod, sl);
    code += "}\n\n";

    code += "void simulate( circuit_state* __restrict const state ) {\n";
    code += ln("simulate_0( state )");
    code += "}\n";

    ModuleCode mc(g, mod);
    mc.codeString = code;
    mc.structLayout = sl.getVarDecls();
    return mc;
  }

}
