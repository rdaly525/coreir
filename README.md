[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)

## Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

## How to Install from source
If you are using osx:
include `export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir>/lib` in your bashrc/.profile 

If you are using linux:
include `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir>/lib` in your bashrc/.profile 

 To Install:
    
    `make install`

  To verify coreir build
    
    `make install`

## How to use coreIR in your C++ project
```
//(in main.cpp)

//include all coreir functions
#include "coreir.h"


int main(...) {
...
}

```

## Libraries
A coreir library `NAME` defines a C++ function `CoreIRLoadLibrary_NAME` that
instantiates and populates a `Namespace` object.  Here is an example defining a
library named **stdlib**.

1) We begin with a header file that declares both the C++ and C interfaces.
   CoreIR provides macros (defined in `coreir-macros.h`) for convenience.
   **NOTE:** The use of the `ifdef` guard for C++ is required.
   ```cpp
   // coreir-stdlib.h
   #ifndef COREIR_STDLIB_H_
   #define COREIR_STDLIB_H_
   
   #include "coreir-macros.h"
   #include "coreir-c/ctypes.h"
   
   #ifdef __cplusplus
   #include "coreir.h"
   COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(stdlib);
   #endif
   
   COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(stdlib);
   
   
   #endif //COREIR_STDLIB_HPP_
   ```

2) Next we define `CoreIRLoadLibrary_stdlib` with the interface `Namespace* CoreIRLoadLibrary_{{NAME}}(Context* c)`
   ```cpp
   // coreir-stdlib.cpp
   #include <coreir-stdlib.h>
   Namespace* CoreIRLoadLibrary_stdlib(Context* c) {
     Namespace* stdlib = c->newNamespace("stdlib");
     stdlib->newNamedType("clk","clkIn",c->Bit());
     return stdlib;
   }
   ```

3) Finally, the library must wrap this function with a C compatible version using
   the macro `COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY`.
   ```cpp
   COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(stdlib);
   ```

To find a full working example see [src/lib/libs/stdlib.cpp](src/lib/libs/stdlib.cpp) and
[include/coreir-lib/stdlib.h](include/coreir-lib/stdlib.h).
