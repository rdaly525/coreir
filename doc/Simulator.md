# Simulating coreir circuits

CoreIR includes a Verilator-style simulator that compiles CoreIR circuits into
C++ code to simulate one cycle of execution of the circuit. To generate simulator
code for add4.json enter the command:

`>./bin/simulator -i examples/add4.json`

This will generate

Then compile the resulting code with:

`>clang++ -std=c++11 -c ./add4_sim.cpp`

# Interpreting CoreIR circuits

CoreIR also inclues a circuit interpreter that can be run from the command line or
through a CoreIR C++ API.

To see some examples of how to use the interpreter through the C++ API
look at the unit tests in ./tests/simulator/interpreter.cpp