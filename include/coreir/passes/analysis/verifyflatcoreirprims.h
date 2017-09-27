#ifndef VERIFYFLATCOREIRPRIMS_H_
#define VERIFYFLATCOREIRPRIMS_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

	class VerifyFlatCoreirPrims : public InstanceGraphPass {
	public :
		static std::string ID;
	  VerifyFlatCoreirPrims() : InstanceGraphPass(ID, "Verify all instances have been flattened", true) {}
		bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
	}; /* class VerifyFlatCoreirPrims */

} /* namespace CoreIR */
} /* namespace Passes */

#endif
