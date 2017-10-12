[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)

## Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

## How to Install from source
### If you are using osx:  
Add `export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir>/lib` to your `~/.bashrc` or `~/.profile`

### If you are using linux:  
Add `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir>/lib` to your `~/.bashrc` or `~/.profile` 

### To Install:
    
    cd <path_to_coreir>
    make install
    
Note: To specify a specific version of `g++` (typically required on older, shared Linux systems), set the `CXX` variable in the make command (e.g. `make install CXX=g++-4.9`)

### To verify coreir build
    
    make test

### Install standalone binary

    make coreir

## Python Bindings
[https://github.com/leonardt/pycoreir](https://github.com/leonardt/pycoreir)
