
## Quick Install (Linux Only):
    wget https://github.com/rdaly525/coreir/releases/download/v0.0.45/coreir.tar.gz
    tar -zxf coreir.tar.gz
    cd release
    sudo make install


## If you do not want to sudo make install:
Option 1: you could provide use `cmake DCMAKE\_INSTALL\_PREFIX=\<path\> ..`

Option 2:
#### If you are using osx:  
Add `export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir_release>/lib` to your `~/.bashrc` or `~/.profile`
If this does not work, you may have System Integrity Protection enabled on your Mac.

#### If you are using linux:  
Add `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir_release>/lib` to your `~/.bashrc` or `~/.profile` 

#### If you are using CMake:
Add the below lines in your `CMakeLists.txt`. (No `PATH` variable needs to be set.)

``` cmake
# CMakeLists.txt

find_package(coreir REQUIRED)

target_link_libraries(MyTarget coreir::coreir)
```

For non-standard install path (`/usr` or `/usr/local`), set `CMAKE_PREFIX_PATH` to the customed install path.

``` bash
# bash
cmake .. -DCMAKE_PREFIX_PATH=<coreir/install/path>
```
 

# How to Install from source (OSX or Linux)

### Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

Note: To specify a specific version of `g++` (typically required on older, shared Linux systems), set the `CXX` variable in the make command (e.g. `make install CXX=g++-4.9`)

### To build:

    git clone https://github.com/rdaly525/coreir.git
    cd coreir/build
    cmake ..
    make -j<num_processors>
    sudo make install

### To verify coreir build
    
    cd coreir
    make -j test

### install to /usr/local
  
    cd coreir/build
    sudo make install

### clean uninstall of coreir 
    cd coreir
    sudo make uninstall

## Python Bindings
[https://github.com/leonardt/pycoreir](https://github.com/leonardt/pycoreir)
