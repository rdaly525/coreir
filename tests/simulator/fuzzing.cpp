#include "fuzzing.hpp"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"
#include "coreir/simulator/print_c.h"

// #include "../src/simulator/algorithm.hpp"
// #include "../src/simulator/sim.hpp"
// #include "../src/simulator/print_c.hpp"
// #include "../src/simulator/output.hpp"

#include <limits.h>
#include <unistd.h>

#include <fstream>
#include <iostream>

#include <cstdlib>

using namespace std;

namespace CoreIR {

  std::string primitiveRandomInputString(CoreIR::Type& t, const std::string& var) {
    assert(isPrimitiveType(t));

    string val = to_string(rand() % 100);

    return ln(var + " = " + val);
  }

  std::string randomInputString(CoreIR::Type& tp, const std::string& var) {
    if (isPrimitiveType(tp)) {
      return primitiveRandomInputString(tp, var);
    }

    if (isArray(tp)) {

      ArrayType& tArr = static_cast<ArrayType&>(tp);
      Type& underlying = *(tArr.getElemType());

      string res = "";
      for (uint i = 0; i < tArr.getLen(); i++) {
	res += randomInputString(underlying, var + "[ " + to_string(i) + " ]");
      }

      return res;
      
    }

    assert(false);
  }

  std::string randomSimInputString(Module* mod) {
    auto args = sortedSimArgumentPairs(*mod);

    string res = "";
    for (auto& arg : args) {
      res += randomInputString(*(arg.first), arg.second);
    }

    return res;
  }

  std::string declareInputs(Module& mod) {
    //    assert(false);
    string res;

    auto args = sortedSimArgumentPairs(mod); //simInputs(mod);

    for (auto& arg : args) {
      res += ln(cArrayTypeDecl(*(arg.first), arg.second));
    }

    return res;
  }

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simOutputVarDecls(Module& mod) {
    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<pair<Type*, string>> declStrs;

    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (!tp->isInput()) {
	assert(tp->isOutput());

	declStrs.push_back({tp, name_type_pair.first});
      }
    }

    return declStrs;
  }
  
  std::string declareOutputs(Module& mod) {
    string res;

    auto args = simOutputVarDecls(mod);

    for (auto& arg : args) {
      res += ln(cArrayTypeDecl(*(arg.first), arg.second));
    }

    return res;
  }

  std::string callSimulate(Module& mod) {
    // vector<string> args;

    // for (auto& arg : simOutputVarDecls(mod)) {
    //   args.push_back("&" + arg.second);
    // }

    // vector<pair<Type*, string> > decls = simInputs(mod);

    // sort_lt(decls, [](const pair<Type*, string>& tpp) {
    // 	return tpp.second;
    //   });

    // for (auto& arg : decls) {
    //   args.push_back(arg.second);
    // }

    string res = ln("std::clock_t    start");
    res += ln("start = std::clock()");
    res += ln("simulate( &state )");
    res += ln("std::cout << \"Time: \" << (std::clock() - start) / (double)(CLOCKS_PER_SEC / 1000) << \" ms\" << std::endl");

    return res;
  }
  
  std::string randomSimInputHarness(Module* mod) {
    string res = "#include <stdint.h>\n";
    res += "#include <ctime>\n";
    res += "#include <iostream>\n\n";
    res += "#include \"many_ops.h\"\n\n";
    res += "int main() {\n";

    res += ln("circuit_state state");
    // res += declareInputs(*mod);
    // res += declareOutputs(*mod);

    // res += randomSimInputString(mod);

    res += callSimulate(*mod);

    res += "}\n";

    return res;
  }

  int generateHarnessAndRun(const std::deque<vdisc>& topoOrder,
			    NGraph& g,
			    Module* mod,
			    const std::string& codeDir,
			    const std::string& outFileBase,
			    const std::string& harnessFile) {

    string hFile = outFileBase + ".h";
    string codeFile = outFileBase + ".cpp";

    writeFiles(topoOrder, g, mod, codeDir, codeFile, hFile);

    std::string harnessCode = randomSimInputHarness(mod);
    std::ofstream out(harnessFile);
    out << harnessCode;
    out.close();

    cout << "Done generating harness" << endl;

    string codeFilePath = codeDir + codeFile;
    string runCmd = "clang++ -lpthread -std=c++11 " + codeFilePath + " " + harnessFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    string runTest = "./a.out";
    int r = system(runTest.c_str());

    cout << "Test result = " << r << endl;

    return s || r;
  }

  void appendStdLib(const std::string& verilogFile) {

    std::ifstream t(verilogFile);
    std::string str((std::istreambuf_iterator<char>(t)),
		    std::istreambuf_iterator<char>());

    str = "`include \"stdlib.v\"\n" + str;

    std::ofstream out(verilogFile);
    out << str;
    out.close();      
    
  }

  int buildVerilator(Module* m,
		     Namespace* g) {
    string modName = m->getName();

    string jsonFile = modName + ".json";
    string verilogFile = modName + ".v";

    // Save namespace to json
    saveToFile(g, jsonFile);

    // Use coreir to compile json into verilog
    string runCmd =
      "../../bin/coreir -i " + jsonFile + " " + " -o " + verilogFile;
    int s = system(runCmd.c_str());

    appendStdLib(verilogFile);

    // Auto generating main file
    string mainFileLoc = "./gencode/" + modName + "Main.cpp";
    string mainStr = "#include <iostream>\n\nusing namespace std;\nint main() {\n\ncout << \"HELLO WORLD!!\" << endl;\n}\n";
    
    std::ofstream out(mainFileLoc);
    out << mainStr;
    out.close();      

    // Run verilator on the resulting file
    string compileVerilator = "verilator -O3 -Wall -Wno-DECLFILENAME --cc " +
      verilogFile + " --exe " + mainFileLoc + " --top-module " + modName;

    s = s || system(compileVerilator.c_str());

    // Build the resulting C++ code
    string mkFile = "V" + modName + ".mk";
    string exeFile = "V" + modName;
    string compileCpp = "make -C obj_dir -j -f " + mkFile + " " + exeFile;

    char result[ PATH_MAX ];
    ssize_t count = readlink( "/proc/self/exe", result, PATH_MAX );
    string res = std::string( result, (count > 0) ? count : 0 );

    cout << "Exe dir = " << res << endl;
    cout << "Verilator compile command = " << compileVerilator << endl;    
    cout << "Compile command = " << compileCpp << endl;

    s = s || system(compileCpp.c_str());

    cout << "DONE COMPILING" << endl;

    // Run the resulting executable
    string runObj = "./obj_dir/" + exeFile;
    s = s || system(runObj.c_str());

    return s;
  }

  
}
