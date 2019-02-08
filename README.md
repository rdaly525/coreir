[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)

## CoreIR
  An LLVM-style hardware compiler with first class support for generators

## Installation Instructions
  Found [here](INSTALL.md)

## License
  CoreIR is open source under the terms of the freeBSD license found in this [license file](LICENSE.txt)

## Documentation

### Documentation for Users
  * This [document](doc/Standalone.md) describes the standalone coreir tool (similar to LLVM's 'opt')
  * This is the [specification](doc/JsonSpec.md) for the CoreIR serialization format (hardware object file)
  * This is a [specification](doc/coreirprims.csv) of CoreIR Primitives and Primitive Extentions


### Documentation for Developers
  * This [Getting Started Guide](doc/GettingStarted.md) provides an introduction and in depth look at how to use the CoreIR C++ API
  * This [Compilation Passes Guide](doc/WritingPasses.md) describes the process of creating new compilation passes
  * This [Library Guide](doc/LibraryGuide.md) talks about creating standalone CoreIR compatible Libraries
  * This [Guide](doc/Simulator.md) describes how to simulate CoreIR hardware graphs
  * This [Style Guide](doc/Style.md) discusses expected coding style for CoreIR

## Bugs and Feature Requests
Please submit an issue through github
