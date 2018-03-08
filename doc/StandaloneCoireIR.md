# The Standalone CoreIR Binary
This tool is meant to work similar to llvm's 'opt'. You can take an input json file, run compiler passes on it, and output to either coreir (.json), verilog (.v), magma (.py), dot (.txt)
For loading external libraries, either specify the full path to the libcoreir-<libname>.so file, or it will search in the following paths for a libcoreir-<libname>.so if you just specify <libname>: /usr/local/lib:/usr/lib:$DYLD_LIBRARY_PATH:$LD_LIBRARY_PATH

## To make
  `make coreir`

## To run
  `./bin/coreir <options>`
  
## Options
From the -h flag

```
>./bin/coreir
a simple hardware compiler
Usage:
  coreir [OPTION...]

  -h, --help             help
  -v, --verbose          Set verbose
  -i, --input arg        input file: <file>.json
  -o, --output arg       output file: <file>.<json|fir|v|py|dot>
  -p, --passes arg       Run passes in order: '<pass1>,<pass2>,<pass3>,...'
  -e, --load_passes arg  external passes:
                         '<path1.so>,<path2.so>,<path3.so>,...'
  -l, --load_libs arg    external libs:
                         '<libname0>,<path/libname1.so>,<libname2>,...'
  -n, --namespaces arg   namespaces to output:
                         '<namespace1>,<namespace2>,<namespace3>,...' (default: global)
  -t, --top arg          top: <namespace>.<modulename>


Analysis Passes
  verifyflattenedtypes
  verifyconnectivity-onlyinputs
  verifyconnectivity-onlyinputs-noclkrst
  verifyinputconnections
  coreirjson
  smv
  verilog
  smtlib2
  hellomodule2
  printer
  createinstancegraph
  firrtl
  createcombview
  verifyconnectivity
  verifyflatcoreirprims
  verifyconnectivity-noclkrst
  createfullinstancemap
  magma

Transform Passes
  transform2combview
  registerinputs
  clockifyinterface
  sanitize-names
  packbitconstants
  adddirected
  cullgraph
  flattentypes
  rungenerators
  fold-constants
  flatten
  removepassthroughs
  cullzexts
  removeunconnected
  unpackconnections
  removebulkconnections
  deletedeadinstances
  removeconstduplicates
  packconnections
  wireclocks-coreir
```
