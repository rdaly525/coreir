#ifndef SIM_OUTPUT_HPP_
#define SIM_OUTPUT_HPP_

#include "coreir/simulator/op_graph.h"

#include <deque>

namespace CoreIR {

  int compileCode(const std::string& code, const std::string& outFile);

  void writeFiles(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& codeFile,
		  const std::string& hFile);

  int compileCodeAndRun(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			Module* mod,
			const std::string& outDir,
			const std::string& baseFileName,
			const std::string& harnessFile);

  void writeBitVectorLib(const std::string& path);  

  int compileCodeAndRun(const std::string& code,
			const std::string& outFile,
			const std::string& harnessFile);
  
  int compileCode(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& outDir,
		  const std::string& baseFileName);

  void writeFiles(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& codePath,
		  const std::string& codeFile,
		  const std::string& hFile);
  
}

#endif
