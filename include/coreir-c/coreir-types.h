typedef enum {
  COREBitTypeKind=0,
  COREBitInTypeKind=1,
  COREArrayTypeKind=2,
  CORERecordTypeKind=3,
  CORENamedTypeKind=4,
} CORETypeKind;

//TODO deal with getDir and Direction enum
//TODO isInput, isOutput, isMixed, isUnknown

//General functions on Types

//Get the Type Kind enum
extern CORETypeKind COREGetTypeKind(COREType* type);

//Get the flipped version of the type
extern COREType* COREFlip(COREType* type);
extern uint CORETypeGetSize(COREType* type);

//print type to stdout
extern void COREPrintType(COREType* t);

//Type constructors
extern COREType* COREBitIn(COREContext* CORE);
extern COREType* COREBit(COREContext* CORE);
extern COREType* COREArray(COREContext* CORE, uint len, COREType* elemType);
extern COREType* CORERecord(COREContext* c, void* recordparams);

//Array type functions
extern uint COREArrayTypeGetLen(COREType* arrayType);
extern COREType* COREArrayTypeGetElemType(COREType* arrayType);

//TODO named and record
