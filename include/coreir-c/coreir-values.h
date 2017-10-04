//This needs to stay the same as CoreIR::Param
//typedef enum {
//  COREIntParam = 0,
//  COREStringParam = 1,
//  CORETypeParam = 2,
//  COREBoolParam = 3
//} COREParam;


//Get the Type Kind enum
extern COREValueType* COREGetValueType(COREValue* arg);

//Create Args
extern COREValue* COREValueBool(COREContext* c,COREBool b);
extern COREValue* COREValueInt(COREContext* c,int i);
extern COREValue* COREValueString(COREContext* c,char* str);

//Arg Getter functions will assert on wrong arg type
extern bool COREValueBoolGet(COREValue* a);
extern int COREValueIntGet(COREValue* a);
extern const char* COREValueStringGet(COREValue* a);
