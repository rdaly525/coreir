[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)


##Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

## How to Install CoreIR

###If you are using a Linux environment:  
  To Install:  
  
    make install
  
  To verify coreir build
    
    make test
  
###If you are using an OSX environment
  To Install:
    
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
COREIR = <Path_to_coreir>
INCS = $COREIR/include
LPATH = $COREIR/bin
LIBS =  -Wl,-rpath,$COREIR/bin -lcoreir-passes -lcoreir
executable: main.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o executable main.o $(LPATH) $(LIBS) 

```

##More to come
