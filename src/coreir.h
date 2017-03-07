//This is for the C API
struct C_CoreIRContext;
typedef struct C_CoreIRContext C_CoreIRContext;

extern C_CoreIRContext* C_newContext();
extern void C_deleteContext(C_CoreIRContext*);
