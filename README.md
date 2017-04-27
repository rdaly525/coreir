[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)


##Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

## How to Install CoreIR

###If you are using a Linux environment:  
  To Install:  
  
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir>/bin  
    make install
  
  To verify coreir build
    
    make test
  
###If you are using an OSX environment
  To Install:
    
    export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir>/bin
    make installosx

  To verify coreir build
    
    make test

## How to use coreIR in your C++ project
```
//(in main.cpp)

//include all coreir functions
#include "coreir.h"

//Optionally include stdlib
#include "coreir-libs/stdlib.hpp"

//Optionally include compiler passes
#include "coreir-passes/passes.hpp"



int main(...) {
...
}

```

```
#Makefile example
INCS = <Path_to_coreir>/include
LPATH = <Path_to_coreir>/bin
LIBS =  -lcoreir-stdlib -lcoreir-passes -lcoreir
executable: main.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o executable main.o $(LPATH) $(LIBS) 

```

##More to come
