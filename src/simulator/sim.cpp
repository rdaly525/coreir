#include "coreir/simulator/simulator.h"

#include "coreir/passes/transform/flatten.h"
#include "coreir/passes/transform/rungenerators.h"

#include "coreir/simulator/algorithm.h"
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

    assert(false);
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
      uint containWidth = containerTypeWidth(*(arg1.getWire()->getType()));
      if (containWidth > tw) {

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
    }

    // string compString = expr->cString();
    // Check if this output needs a mask
    if (g.getOutputConnections(vd)[0].first.needsMask()) {
      expr = maskResultExpression(*(outPair.second->getType()), expr);
    }

    return expr;
  }

  LowExpr* castToSigned(Type& tp, LowExpr* const expr) {
    return new LowId(parens(parens(signedCTypeString(tp)) + " " + expr->cString()));
  }

  LowExpr* castToUnSigned(Type& tp, LowExpr* const expr) {
    return new LowId(parens(parens(unSignedCTypeString(tp)) + " " + expr->cString()));
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

    //string res;
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

    //LowProgram prog;
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

    assert(false);
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

    //string s = lp.outputVarName(*wd.getWire()) + " = ";

    string resName = lp.outputVarName(*wd.getWire());

    InstanceValue add = findArg("in", ins);

    string oldValName = lp.outputVarName(*r);

    // Need to handle the case where clock is not actually directly from an input
    // clock variable
    string resStr;
    if (hasEnable(wd.getWire())) {
      //string condition = "";
      LowExpr* condition;
      
      InstanceValue en = findArg("en", ins);
      condition = printOpResultStr(en, g, lp);

      resStr = ite(parens(condition->cString()),
                   printOpResultStr(add, g, lp)->cString(),
                   oldValName); // + ";\n";
    } else {
      resStr = printOpResultStr(add, g, lp)->cString(); // + ";\n";
    }

    //LowProgram prog;
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
        assert(isAddOrSub(*inst));

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

  //vector<string>
  void
  updateSequentialElements(const SIMDGroup& group,
                           NGraph& g,
                           Module& mod,
                           LayoutPolicy& layoutPolicy,
                           LowProgram& prog) {

    //vector<string> simLines;
    auto topoOrder = group.nodes[0];
    
    if (group.nodes.size() == 1) {

      // Update stateful element values

      for (auto& vd : topoOrder) {
        WireNode wd = getNode(g, vd);
        Wireable* inst = wd.getWire();
        if (isInstance(inst)) { 
          if (!isCombinationalInstance(wd) &&
              wd.isReceiver) {
            //LowProgram prog;
            printInstance(wd, vd, g, layoutPolicy, prog);
            //simLines.push_back(prog.cString()); //printInstance(wd, vd, g, layoutPolicy));
          }
        }
      }
    } else {

      assert(false);

      // for (auto& vd : topoOrder) {
      //   WireNode wd = getNode(g, vd);
      //   Wireable* inst = wd.getWire();
      //   if (isInstance(inst)) { 
      //     if (!isCombinationalInstance(wd) &&
      //         wd.isReceiver) {
      //       concat(simLines, printSIMDNode(vd, group.totalWidth, g, mod, layoutPolicy));
      //     }
      //   }
      // }
      
    }

    //return simLines;

  }

  //LowProgram
  void
  updateCombinationalLogic(const std::deque<vdisc>& topoOrder,
                           NGraph& g,
                           Module& mod,
                           LayoutPolicy& layoutPolicy,
                           LowProgram& prog) {
    vector<string> simLines;

    int i = 0;

    //LowProgram prog;
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

    //return prog;

    // simLines.push_back(prog.cString());

    // return simLines;
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

  //vector<vector<SubDAG> >
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

    // vector<string> simLines;
    // SubDAG init = group.nodes[0];

    // string tmp = cVar(*(g.getNode(init[0]).getWire()));    

    // // Emit SIMD code for each node in the pattern
    // for (auto& vd : init) {
    //   WireNode wd = g.getNode(vd);
    //   if (!wd.isSequential || !wd.isReceiver) {
    //     concat(simLines, printSIMDNode(vd, group.totalWidth, g, mod, lp));
    //   }
    // }

    // return simLines;
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

  void addDAGCode(const std::vector<SIMDGroup>& dags,
                  NGraph& g,
                  Module& mod,
                  LayoutPolicy& layoutPolicy,
                  LowProgram& prog) {
                  //std::vector<std::string>& simLines) {

    for (auto& simdGroup : dags) {
      //concat(simLines, printSIMDGroup(simdGroup, g, mod, layoutPolicy, prog));
      printSIMDGroup(simdGroup, g, mod, layoutPolicy, prog);
    }

  }

  struct CodeGroup {
    std::vector<SIMDGroup> dags;
    bool sequentialUpdate;
  };

  void addDAGCode(const CodeGroup& code,
                  NGraph& g,
                  Module& mod,
                  LayoutPolicy& layoutPolicy,
                  LowProgram& prog) {
                  //std::vector<std::string>& simLines) {
    if (!code.sequentialUpdate) {
      //LowProgram prog;
      addDAGCode(code.dags, g, mod, layoutPolicy, prog);
      //simLines.push_back(prog.cString());
    } else {
      for (auto& dag : code.dags) {
        //LowProgram prog;
        updateSequentialElements(dag, g, mod, layoutPolicy, prog);
        //simLines.push_back(prog.cString());
        //concat(simLines, updateSequentialElements(dag, g, mod, layoutPolicy));
      }
    }
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

  string printSimFunctionBody(const std::deque<vdisc>& topoOrder,
                              NGraph& g,
                              Module& mod,
                              LayoutPolicy& layoutPolicy) {

    string str = printSimFunctionPrefix(topoOrder, g, mod);

    // Print out operations in topological order
    str += "\n// Simulation code\n";

    vector<string> simLines;

    auto paths = buildCircuitPaths(topoOrder, g, mod);
    // paths.postSequentialDAGs = optimizeSIMD(paths.postSequentialDAGs,
    //                                         g,
    //                                         mod,
    //                                         layoutPolicy);
    // paths.preSequentialDAGs = optimizeSIMD(paths.preSequentialDAGs,
    //                                        g,
    //                                        mod,
    //                                        layoutPolicy);

    auto clk = findMainClock(g);

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

      vector<CodeGroup> codeGroups;

      codeGroups.push_back({paths.preSequentialDAGs, false});
      
      vector<SIMDGroup> allUpdates;
      concat(allUpdates, paths.postSequentialDAGs);
      concat(allUpdates, paths.preSequentialDAGs);
      concat(allUpdates, paths.postSequentialAlwaysDAGs);
      concat(allUpdates, paths.preSequentialAlwaysDAGs);

      allUpdates = deleteDuplicates(allUpdates);

      codeGroups.push_back({allUpdates, true});

      codeGroups.push_back({paths.postSequentialDAGs, false});

      LowProgram clkProg;
      for (auto& group : codeGroups) {
        addDAGCode(group, g, mod, layoutPolicy, clkProg);
      }
      simLines.push_back(clkProg.cString());
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

    code += "void simulate_0( circuit_state* __restrict state ) {\n";
    code += printSimFunctionBody(topoOrder, g, *mod, sl);
    code += "}\n\n";

    code += "void simulate( circuit_state* state ) {\n";
    code += ln("simulate_0( state )");
    code += "}\n";

    ModuleCode mc(g, mod);
    mc.codeString = code;
    mc.structLayout = sl.getVarDecls();
    return mc;
  }

}
