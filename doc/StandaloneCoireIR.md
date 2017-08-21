# The Standalone CoreIR Binary
This tool is meant to work similar to llvm's 'opt'. You can take an input json file, run compiler passes on it, and output to either coreir (.json), firrtl (.fir) or verilog (.v)

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
  -o, --output arg       output file: <file>.<json|fir|v|dot>
  -p, --passes arg       Run passes in order: '<pass1>,<pass2>,<pass3>,...'
  -e, --load_passes arg  load external passes:
                         '<path1.so>,<path2.so>,<path3.so>,...'
  -l, --load_libs arg    load external libs:
                         '<path1.so>,<path2.so>,<path3.so>,...'
  -n, --namespaces arg   namespaces to output:
                         '<namespace1>,<namespace2>,<namespace3>,...' (default: _G)


Analysis Passes
  strongverify
  coreirjson
  weakverify
  createinstancemap
  verilog
  constructInstanceGraph
  firrtl
  verifyflattenedtypes
  helloa

Transform Passes
  removebulkconnections
  flattentypes
  rungenerators
  liftclockports-coreir
  hellot
  wireclocks-coreir
  flatten
```