# Simulating coreir circuits

CoreIR includes a Verilator-style simulator that compiles CoreIR circuits into
C++ code to simulate one cycle of execution of the circuit. To generate simulator
code for add4.json enter the command:

`>./bin/simulator -i examples/add4.json`

This will generate 3 C++ files: add4_sim.cpp, add4_sim.h, and bit_vector.h.

bit_vector.h is a utility function that you can ignore.

If you open add4_sim.h contains a struct representing the state of the circuit
and the declaration of the simulation function:

```cpp
#include <stdint.h>
#include <cstdio>

#include "bit_vector.h"

using namespace bsim;

struct circuit_state {
	uint16_t self_in_0;
	uint16_t self_in_1;
	uint16_t self_in_2;
	uint16_t self_in_3;
	uint16_t self_out;
};

void simulate( circuit_state* state );

```

The function ``` void simulate( circuit_state* state ); ``` simulates a single cycle
of execution.

The code for ```simulate``` is located in add4_sim.cpp and should look like so:

```cpp
#include "add4_sim.h"
#include <thread>

using namespace bsim;

#define SIGN_EXTEND(start, end, x) (((x) & ((1ULL << (start)) - 1)) | (((x) & (1ULL << ((start) - 1))) ? (((1ULL << ((end) - (start))) - 1) << (start)) : 0))

#define MASK(width, expr) (((1ULL << (width)) - 1) & ((expr)))

void simulate_0( circuit_state* state ) {

// Variable declarations

// Internal variables
uint16_t  i01_out;
uint16_t  i00_out;
uint16_t  i1_out;

// Simulation code
(state->self_out) = (((state->self_in_0) + (state->self_in_1)) + ((state->self_in_2) + (state->self_in_3)));
}

void simulate( circuit_state* state ) {
simulate_0( state );
}

```

You can compile the resulting code with:

`>clang++ -std=c++11 -c ./add4_sim.cpp`

# Interpreting CoreIR circuits

CoreIR also inclues a circuit interpreter that can be run from the command line or
through a CoreIR C++ API.

To see some examples of how to use the interpreter through the C++ API
look at the unit tests in [../tests/simulator/interpreter.cpp](../tests/simulator/interpreter.cpp).