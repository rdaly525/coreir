#include "sim.hpp"

#include "coreir-passes/transform/flatten.h"
#include "coreir-passes/transform/rungenerators.h"

#include "algorithm.hpp"
#include "print_c.hpp"
#include "utils.hpp"

using namespace CoreIR;
using namespace CoreIR::Passes;

namespace CoreIR {

  string printUnop(Instance* inst, const vdisc vd, const NGraph& g) {
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 1);

    Conn cn = (*std::begin(inConns));
    Wireable* arg = cn.first.getWire();
    
    Wireable* dest = inConns[0].second.getWire();
    assert(isSelect(dest));

    Select* destSel = toSelect(dest);
    assert(destSel->getParent() == inst);

    string opString = getOpString(*inst);

    string res = "";
    if (opString == "~") {
      res += maskResult(*((outPair.second)->getType()), opString + cVar(*arg));
    } else {
      res += opString + cVar(*arg);
    }

    return res;
  }

  string printConstant(Instance* inst, const vdisc vd, const NGraph& g) {

    bool foundValue = false;

    string argStr = "";
    for (auto& arg : inst->getConfigArgs()) {
      if (arg.first == "value") {
	foundValue = true;
	Arg* valArg = arg.second;

	assert(valArg->getKind() == AINT);

	ArgInt* valInt = static_cast<ArgInt*>(valArg);
	argStr = valInt->toString();
      }
    }

    assert(foundValue);

    return argStr;
  }
  
  string printOpThenMaskBinop(const WireNode& wd, const vdisc vd, const NGraph& g) {
    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    string res = "";

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    //res += cVar(*(outPair.second)) + " = ";

    auto inConns = getInputConnections(vd, g);

    assert(inConns.size() == 2);

    WireNode arg1;
    WireNode arg2;

    auto dest = inConns[0].second.getWire();
    assert(isSelect(dest));

    Select* destSel = toSelect(dest);
    assert(destSel->getParent() == inst);

    if (destSel->getSelStr() == "in0") {
      arg1 = inConns[0].first;
      arg2 = inConns[1].first;
    } else {
      arg1 = inConns[1].first;
      arg2 = inConns[0].first;
    }

    string opString = getOpString(*inst);

    string compString = cVar(arg1) + opString + cVar(arg2);

    // And not standard width
    if (isDASHR(*inst)) {
      uint tw = typeWidth(*(arg1.getWire()->getType()));
      uint containWidth = containerTypeWidth(*(arg1.getWire()->getType()));

      assert(containWidth > tw);

      //uint diff = containWidth - tw;
      //string diffStr = parens(to_string(diff) + " + " + cVar(arg2));

      string mask =
	parens(bitMaskString(cVar(arg2)) + " << " + parens(to_string(tw) + " - " + cVar(arg2)));

      string signBitSet =
	parens("0x01 & " + parens(cVar(arg1) +  " >> " + parens(to_string(tw - 1))));

      compString = parens(ite(signBitSet, mask, "0") + " | " + parens(compString));
    }

    assert(wd.highBitsAreDirty());
    assert(!!(wd.highBitsAreDirty()));

    if (wd.highBitsAreDirty()) {
      res += maskResult(*(outPair.second->getType()), compString); // + ";\n";
    } else {
      //res += compString + ";\n";
      //maskResult(*(outPair.second->getType()), compString) + ";\n";
    }
    //res += "\n";

    return res;
  }

  string castToSigned(Type& tp, const std::string& expr) {
    return parens(parens(signedCTypeString(tp)) + " " + expr);
  }

  string seString(Type& tp, const std::string& arg) {
    uint startWidth = typeWidth(tp);
    uint extWidth = containerTypeWidth(tp);

    string mask = parens(arg + " & " + bitMaskString(startWidth));
    string testClause = parens(arg + " & " + parens("1ULL << " + to_string(startWidth - 1)));

    string res = parens(mask + " | " +
			ite(testClause, lastMask(startWidth, extWidth), "0"));

    return res;
  }

  string
  printSEThenOpThenMaskBinop(Instance* inst, const vdisc vd, const NGraph& g) {
      auto outSelects = getOutputSelects(inst);

      assert(outSelects.size() == 1);

      pair<string, Wireable*> outPair = *std::begin(outSelects);

      auto inConns = getInputConnections(vd, g);

      assert(inConns.size() == 2);

      WireNode arg1;
      WireNode arg2;

      auto dest = inConns[0].second.getWire();
      assert(isSelect(dest));

      Select* destSel = toSelect(dest);
      assert(destSel->getParent() == inst);

      if (destSel->getSelStr() == "in0") {
	arg1 = inConns[0].first;
	arg2 = inConns[1].first;
      } else {
	arg1 = inConns[1].first;
	arg2 = inConns[0].first;
      }

      string opString = getOpString(*inst);

      Type& arg1Tp = *((arg1.getWire())->getType());
      Type& arg2Tp = *((arg2.getWire())->getType());

      string res = maskResult(*(outPair.second->getType()),
			      castToSigned(arg1Tp, seString(arg1Tp, cVar(arg1))) +
			      opString +
			      castToSigned(arg2Tp, seString(arg2Tp, cVar(arg2))));

      return res;
  }

  bool isMux(Instance& inst) {

    string genRefName = getInstanceName(inst);

    return genRefName == "mux";

  }

  WireNode findArg(string argName, std::vector<Conn>& ins) {
    for (auto& conn : ins) {
      WireNode arg = conn.first;
      WireNode placement = conn.second;
      string selName = toSelect(placement.getWire())->getSelStr();
      if (selName == argName) {
	return arg;
      }
    }

    cout << "Error: Could not find argument: " << argName << endl;

    assert(false);
  }

  string printMux(Instance* inst, const vdisc vd, const NGraph& g) {
    assert(isMux(*inst));

    // auto outSel = getOutputSelects(inst);

    // assert(outSel.size() == 1);

    // Select* sl = toSelect((*(begin(outSel))).second);

    // assert(isInstance(sl->getParent()));

    // Instance* r = toInstance(sl->getParent());
    // string rName = r->getInstname();

    auto ins = getInputConnections(vd, g);

    assert(ins.size() == 3);

    WireNode sel = findArg("sel", ins);
    WireNode i0 = findArg("in0", ins);
    WireNode i1 = findArg("in1", ins);
    
    // TODO: Replace with assign function that considers types eventually
    //return cVar(*sl) + " = " + ite(cVar(sel), cVar(i1), cVar(i0)) + ";\n";
    return ite(cVar(sel), cVar(i1), cVar(i0));
    
  }

  string printTernop(Instance* inst, const vdisc vd, const NGraph& g) {
    assert(getInputs(vd, g).size() == 3);

    if (isMux(*inst)) {
      return printMux(inst, vd, g);
    }

    assert(false);
  }

  string printBinop(const WireNode& wd, const vdisc vd, const NGraph& g) {
    assert(getInputs(vd, g).size() == 2);

    Instance* inst = toInstance(wd.getWire());

    if (isBitwiseOp(*inst) ||
	isSignInvariantOp(*inst) ||
	isUnsignedCmp(*inst) ||
	isShiftOp(*inst) ||
	isUDivOrRem(*inst)) {
      return printOpThenMaskBinop(wd, vd, g);
    }

    if (isSignedCmp(*inst) ||
	isSDivOrRem(*inst)) {
      return printSEThenOpThenMaskBinop(inst, vd, g);
    }

    assert(false);
  }

  string varSuffix(const WireNode& wd) {
    if (wd.isSequential) {
      if (wd.isReceiver) {
	return "_receiver";
      } else {
	return "_source";
      }
    }

    return "";
  }

  bool hasEnable(Wireable* w) {
    assert(isRegisterInstance(w));

    return recordTypeHasField("en", w->getType());
  }

  string enableRegReceiver(const WireNode& wd, const vdisc vd, const NGraph& g) {

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* sl = toSelect((*(begin(outSel))).second);

    assert(isInstance(sl->getParent()));

    Instance* r = toInstance(sl->getParent());
    string rName = r->getInstname();

    auto ins = getInputConnections(vd, g);

    assert(ins.size() == 3);

    string s = "*" + rName + "_new_value = ";
    WireNode clk;
    WireNode en;
    WireNode add;

    for (auto& conn : ins) {
      WireNode arg = conn.first;
      WireNode placement = conn.second;
      string selName = toSelect(placement.getWire())->getSelStr();
      if (selName == "en") {
	en = arg;
      } else if (selName == "clk") {
	clk = arg;
      } else {
	add = arg;
      }
    }

    string oldValName = rName + "_old_value";

    s += ite("(((" + cVar(clk, "_last") + " == 0) && (" + cVar(clk) + " == 1)) && " +
	     cVar(en) + ")",
	     cVar(add),
	     oldValName) + ";\n";
    
    return s;
  }

  string noEnableRegReceiver(const WireNode& wd, const vdisc vd, const NGraph& g) {

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* sl = toSelect((*(begin(outSel))).second);

    assert(isInstance(sl->getParent()));

    Instance* r = toInstance(sl->getParent());
    string rName = r->getInstname();

    auto ins = getInputConnections(vd, g);

    assert(ins.size() == 2);

    string s = "*" + rName + "_new_value = ";
    WireNode clk;
    WireNode add;

    for (auto& conn : ins) {
      WireNode arg = conn.first;
      WireNode placement = conn.second;
      string selName = toSelect(placement.getWire())->getSelStr();
      if (selName == "clk") {
	clk = arg;
      } else {
	add = arg;
      }
    }

    string oldValName = rName + "_old_value";

    s += ite("((" + cVar(clk, "_last") + " == 0) && (" + cVar(clk) + " == 1))",
	     cVar(add),
	     oldValName) + ";\n";

    return s;
  }

  string printRegister(const WireNode& wd, const vdisc vd, const NGraph& g) {
    assert(wd.isSequential);

    auto outSel = getOutputSelects(wd.getWire());

    assert(outSel.size() == 1);
    Select* s = toSelect((*(begin(outSel))).second);

    assert(isInstance(s->getParent()));

    Instance* r = toInstance(s->getParent());
    string rName = r->getInstname();

    if (!wd.isReceiver) {
      return cVar(*s) + varSuffix(wd) + " = " + rName + "_old_value" + " ;\n";
    } else {
      if (hasEnable(wd.getWire())) {
	return enableRegReceiver(wd, vd, g);
      } else {
	return noEnableRegReceiver(wd, vd, g);
      }
    }
  }

  string opResultStr(const WireNode& wd, const vdisc vd, const NGraph& g) {
    Instance* inst = toInstance(wd.getWire());
    auto ins = getInputs(vd, g);
    
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);
    string res = cVar(*(outPair.second));
    
    if (ins.size() == 3) {
      return printTernop(inst, vd, g);
    }

    if (ins.size() == 2) {
      return printBinop(wd, vd, g);
    }

    if (ins.size() == 1) {
      return printUnop(inst, vd, g);
    }

    if (ins.size() == 0) {

      return printConstant(inst, vd, g);
    }

    cout << "Unsupported instance = " << inst->toString() << endl;
    assert(false);
    
  }

  string printOp(const WireNode& wd, const vdisc vd, const NGraph& g) {
    Instance* inst = toInstance(wd.getWire());
    auto ins = getInputs(vd, g);
    
    if (isRegisterInstance(inst)) {
      return printRegister(wd, vd, g);
    }

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);
    string res = cVar(*(outPair.second));

    return ln(res + " = " + opResultStr(wd, vd, g));
  }

  string printOpResultStr(const WireNode& wd, const NGraph& g) {
    assert(isSelect(wd.getWire()));

    if (isRegisterInstance(extractSource(toSelect(wd.getWire())))) {
      return cVar(wd);
    }

    Wireable* sourceInstance = extractSource(toSelect(wd.getWire()));

    cout << "Source of " << wd.getWire()->toString() << " is " << sourceInstance->toString() << endl;

    if (isSelect(sourceInstance)) {
      return cVar(wd);
    }

    assert(g.containsOpNode(sourceInstance));

    vdisc opNodeD = g.getOpNodeDisc(sourceInstance);

    // TODO: Should really check whether or not there is one connection using
    // the given variable
    if (g.getOutputConnections(opNodeD).size() == 1) {
      //return cVar(wd);
      return opResultStr(combNode(sourceInstance), opNodeD, g);
    }

    assert(false);
  }

  bool fromSelfInterface(Select* w) {
    if (!fromSelf(w)) {
      return false;
    }

    Wireable* parent = w->getParent();
    if (isInterface(parent)) {
      return true;
    } else if (isInstance(parent)) {
      return false;
    }

    assert(isSelect(parent));

    return fromSelf(toSelect(parent));
  }

  bool arrayAccess(Select* in) {
    return isNumber(in->getSelStr());
  }

  std::unordered_map<string, Type*>
  outputs(Module& mod) {
    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    unordered_map<string, Type*> outs;

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<string> declStrs;
    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (tp->isOutput()) {
	outs.insert(name_type_pair);
      }
    }

    return outs;
    
  }

  string copyTypeFromInternal(Type* tp,
			      const std::string& toName,
			      const std::string& fromName) {
    if (isPrimitiveType(*tp)) {
      return toName + " = " + fromName + "; // copyTypeFromInternal\n";
    }

    if (isArray(*tp)) {
      ArrayType* arr = static_cast<ArrayType*>(tp);

      string res = "";
      for (uint i = 0; i < arr->getLen(); i++) {
	string acc = "[ " + std::to_string(i) + " ]";
	string accName = toName + acc;
	string accFrom = fromName + acc;
	res += copyTypeFromInternal(arr->getElemType(), accName, accFrom) + "\n";
      }

      return res;
    }

    cout << "Failed for type = " << tp->toString() << endl;
    cout << "         toName = " << toName << endl;
    cout << "       fromName = " << fromName << endl;
    assert(false);
  }  

  string copyTypeFromInternal(Type* tp,
			      const std::string& field_name) {
    return copyTypeFromInternal(tp,
				"(*self_" + field_name + "_ptr)",
				"self_" + field_name);
  }

  string printInternalVariables(const std::deque<vdisc>& topo_order,
				NGraph& g,
				Module& mod) {
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
		str += cArrayTypeDecl(*(in->getType()), " " + cVar(*in) + "_receiver") + ";\n";

	      } else {
		str += cArrayTypeDecl(*(in->getType()), " " + cVar(*in) + "_source") + ";\n";

	      }
	    }
	  }
	}
      }
    }

    return str;
  }

  string printSimFunctionBody(const std::deque<vdisc>& topo_order,
			      NGraph& g,
			      Module& mod) {
    string str = "";
    // Declare all variables
    str += "\n// Variable declarations\n";

    str += "\n// Outputs\n";

    for (auto& name_type_pair : outputs(mod)) {
      Type* tp = name_type_pair.second;
      str += cArrayTypeDecl(*tp, "self_" + name_type_pair.first) + ";\n";
    }
  
    str += "\n// Internal variables\n";
    str += printInternalVariables(topo_order, g, mod);

    // Print out operations in topological order
    str += "\n// Simulation code\n";
    for (auto& vd : topo_order) {

      WireNode wd = getNode(g, vd);
      Wireable* inst = wd.getWire();

      if (isInstance(inst)) {
	str += printOp(wd, vd, g);
      } else {

	if (inst->getType()->isInput()) {

	  auto inConns = getInputConnections(vd, g);

	  // If not an instance copy the input values
	  for (auto inConn : inConns) {

	    //str += ln(cVar("(*", *(inConn.second.getWire()), "_ptr)") + " = " + cVar(inConn.first));
	    
	    str += ln(cVar("(*", *(inConn.second.getWire()), "_ptr)") + " = " + printOpResultStr(inConn.first, g));//cVar(inConn.first));
	  }

	}
      }
    }

    return str;
  }

  bool underlyingTypeIsClkIn(Type& tp) {
    if (isClkIn(tp)) {
      return true;
    }

    if (isArray(tp)) {
      ArrayType& tarr = toArray(tp);
      return underlyingTypeIsClkIn(*(tarr.getElemType()));
    }

    return false;

  }

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simRegisterInputs(Module& mod) {

    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    //RecordType* modRec = static_cast<RecordType*>(tp);
    vector<pair<Type*, string>> declStrs;
    
    // Add register inputs
    for (auto& inst : mod.getDef()->getInstances()) {
      if (isRegisterInstance(inst.second)) {
	Instance* is = inst.second;

	Select* in = is->sel("in");
	Type* itp = in->getType();

	string regName = is->getInstname();

	declStrs.push_back({itp, regName + "_old_value"});
	declStrs.push_back({itp, "(*" + regName + "_new_value)"});
	
      }
    }

    return declStrs;
    
  }
  
  std::vector<std::pair<CoreIR::Type*, std::string> >
  simInputs(Module& mod) {

    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<pair<Type*, string>> declStrs;

    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (tp->isInput()) {
	if (!underlyingTypeIsClkIn(*tp)) {
	  declStrs.push_back({tp, "self_" + name_type_pair.first});
	} else {
	  declStrs.push_back({tp, "self_" + name_type_pair.first});
	  declStrs.push_back({tp, "self_" + name_type_pair.first + "_last"});

	}
      }
    }

    // Add register inputs
    concat(declStrs, simRegisterInputs(mod));

    return declStrs;

  }
  
  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod) {

    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<pair<Type*, string>> declStrs;

    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (tp->isInput()) {
	if (!underlyingTypeIsClkIn(*tp)) {
	  declStrs.push_back({tp, "self_" + name_type_pair.first});
	} else {
	  declStrs.push_back({tp, "self_" + name_type_pair.first});
	  declStrs.push_back({tp, "self_" + name_type_pair.first + "_last"});

	}
      } else {
	assert(tp->isOutput());

	declStrs.push_back({tp, "(*self_" + name_type_pair.first + "_ptr)"});
      }
    }

    // Add register inputs
    concat(declStrs, simRegisterInputs(mod));

    return declStrs;
    
  }

  std::vector<string> sortedSimArgumentList(Module& mod) {

    auto decls = sortedSimArgumentPairs(mod);

    sort_lt(decls, [](const pair<Type*, string>& tpp) {
	return tpp.second;
      });

    vector<string> declStrs;
    for (auto declPair :  decls) {
      declStrs.push_back(cArrayTypeDecl(*(declPair.first), declPair.second));
    }

    return declStrs;
  }

  string printSimArguments(Module& mod) {

    auto declStrs = sortedSimArgumentList(mod);
    // Print out declstrings
    string res = commaSepList(declStrs);

    return res;
  }

  string printDecl(CoreIR::Module* mod) {
    string code = "";
    code += "#include <stdint.h>\n";
    code += "#include <cstdio>\n";

    code += "void simulate( ";

    code += printSimArguments(*mod);

    code += + " );";

    return code;
  }

  string printCode(const std::deque<vdisc>& topoOrder,
		   NGraph& g,
		   CoreIR::Module* mod) {

    string code = "";

    code += "#include <stdint.h>\n";
    code += "#include <cstdio>\n";

    code += "void simulate( ";

    code += printSimArguments(*mod);

    code += + " ) {\n";

    code += printSimFunctionBody(topoOrder, g, *mod);

    code += "}\n";

    return code;
  }


}
