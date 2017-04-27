#define COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(NAME) extern "C" CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c) { \
  return reinterpret_cast<CORENamespace*>(CoreIRLoadLibrary_ ## NAME(reinterpret_cast<CoreIR::Context*>(c))); \
}

#define COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(NAME) CoreIR::Namespace* CoreIRLoadLibrary_ ## NAME(CoreIR::Context* c)

#define COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(NAME) extern "C" CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c)
