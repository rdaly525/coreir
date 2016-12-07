#ifndef ENUMS_HPP_
#define ENUMS_HPP_

// Figure out easy file/line debug
#define DEBUGINFO __FILE__ << ":" << __LINE__

#include <stdint.h>

typedef uint32_t uint;

typedef enum {INT,ARRAY,RECORD} TypeEnum;
typedef enum {IN,OUT} Dir;
typedef enum {IFACE,INST,SEL} WireableEnum;
typedef enum {MDEF,MDEC,GDEC,GDEF} InstantiableEnum;


#endif //ENUMS_HPP_
