
## Quick Install (Linux Only):
    wget https://github.com/rdaly525/coreir/releases/download/v0.0.3/coreir.tar.gz
    tar -zxf coreir.tar.gz
    cd release
    sudo make install

### Uninstall:
    
    make uninstall

## How to Install from source (OSX or Linux)

### Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

### If you are using osx:  
Add `export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir>/lib` to your `~/.bashrc` or `~/.profile`

### If you are using linux:  
Add `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir>/lib` to your `~/.bashrc` or `~/.profile` 

    
Note: To specify a specific version of `g++` (typically required on older, shared Linux systems), set the `CXX` variable in the make command (e.g. `make install CXX=g++-4.9`)

### To build:

    git clone https://github.com/rdaly525/coreir.git
    cd coreir
    make -j

### To verify coreir build
    
    make -j test

### create standalone binary

    make -j coreir

### install to /usr or /usr/bin 
  
    sudo make install

### clean uninstall of coreir 

    sudo make uninstall

## Python Bindings
[https://github.com/leonardt/pycoreir](https://github.com/leonardt/pycoreir)
