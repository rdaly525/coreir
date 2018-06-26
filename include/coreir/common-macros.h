#ifdef __cplusplus
#define COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(NAME) extern "C" CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c) { \
  return reinterpret_cast<CORENamespace*>(CoreIRLoadLibrary_ ## NAME(reinterpret_cast<CoreIR::Context*>(c))); \
}
#else
#define COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(NAME) CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c) { \
  return reinterpret_cast<CORENamespace*>(CoreIRLoadLibrary_ ## NAME(reinterpret_cast<CoreIR::Context*>(c))); \
}
#endif

#define COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(NAME) CoreIR::Namespace* CoreIRLoadLibrary_ ## NAME(CoreIR::Context* c)

#ifdef __cplusplus
#define COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(NAME) extern "C" CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c)
#else
#define COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(NAME) CORENamespace* CORELoadLibrary_ ## NAME(COREContext* c)
#endif

#define COREIR_GEN_EXTERNAL_PASS(NAME) extern "C" CoreIR::Pass* registerPass() { \
  return new NAME(); \
}

#define COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(NAME) extern "C" CoreIR::Namespace* ExternalLoadLibrary_ ## NAME(CoreIR::Context* c) { \
  return CoreIRLoadLibrary_ ## NAME(c); \
}
