
## Quick Install Release:
    # Uncomment one of the following lines to choose your OS
    # export OS_NAME="linux"
    # export OS_NAME="osx"

    # Fetch the latest release from GitHub
    $ curl -s -L https://github.com/rdaly525/coreir/releases/latest | grep "href.*coreir-${OS_NAME}.tar.gz" | cut -d \" -f 2 | xargs -I {} wget https://github.com"{}"

    # Unpack and install
    $ mkdir coreir_release;
    $ tar -xf coreir-${OS_NAME}.tar.gz -C coreir_release --strip-components 1;
    $ cd coreir_release && sudo make install && cd ..


## If you do not want to sudo make install:
Option 1: you could provide use `cmake DCMAKE\_INSTALL\_PREFIX=\<path\> ..`

Option 2:
#### If you are using osx:  
Add `export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<path_to_coreir_release>/lib` to your `~/.bashrc` or `~/.profile`
If this does not work, you may have System Integrity Protection enabled on your Mac.

### If you are using linux:  
Add `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<path_to_coreir_release>/lib` to your `~/.bashrc` or `~/.profile` 
 

# How to Install from source (OSX or Linux)

### Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  

Note: To specify a specific version of `g++` (typically required on older, shared Linux systems), set the `CXX` variable in the make command (e.g. `make install CXX=g++-4.9`)

#### Dependencies
##### Homebrew
```
brew install cmake
```

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
