
## Libraries
A coreir library `NAME` defines a C++ function `CoreIRLoadLibrary_NAME` that
instantiates and populates a `Namespace` object.  Here is an example defining a
library named **cgralib**.

1) We begin with a header file that declares both the C++ and C interfaces.
   CoreIR provides macros (defined in `coreir-macros.h`) for convenience.
   **NOTE:** The use of the `ifdef` guard for C++ is required.
   
   ```cpp
   // cgralib.h
   #ifndef COREIR_ICE40LIB_H_
   #define COREIR_ICE40LIB_H_
   
   #include "coreir-macros.h"
   #include "coreir-c/ctypes.h"
   
   #ifdef __cplusplus
   #include "coreir.h"
   COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(ice40);
   #endif
   
   COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(ice40);
   
   
   #endif //COREIR_ICE40_HPP_
   ```

2) Next we define `CoreIRLoadLibrary_ice40` with the interface 
`Namespace* CoreIRLoadLibrary_{{NAME}}(Context* c)`

    ```cpp
    // ice40.cpp
    #include <coreir-stdlib.h>
    Namespace* CoreIRLoadLibrary_ice40(Context* c) {
     
      //Create and register new namespace in Context
      Namespace* ice40 = c->newNamespace("ice40");

      //Define a type for the module
      Type* SB_LUT4Type = c->Record({{"I0", c->BitIn()},
                                    {"I1", c->BitIn()},
                                    {"I2", c->BitIn()},
                                    {"I3", c->BitIn()},
                                    {"O",  c->Bit()}});
    
      //Define Config Parameters for the module
      Params SB_LUT4Params({{"LUT_INIT", AINT}});
      
      //Declare the module (Will add this to the ice40 namespace)
      Module* SB_LUT4 = ice40->newModuleDecl("SB_LUT4", SB_LUT4Type, SB_LUT4Params);
      //Optionally add module definition and other options for SB_LUT4
      //...
      
      //Define Rest of modules/generators/NamedTypes
      //...
      
      //return the new namespace
      return ice40;
    }
    ```
3) Next, the library must wrap this function with an API capable of being dynamically loaded from bin/coreir using the macro: `COREIR_GEN_EXTERNAL_API_FOR_LIBRARY`
3) Finally, the library must wrap this function with a C compatible version using the macro `COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY`.

   ```cpp
   COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(ice40)
   COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(ice40);
   ```

To find a full working example see [src/libs/ice40.cpp](../src/libs/ice40.cpp) and
[include/coreir-lib/ice40.h](../include/coreir-lib/ice40.h).
