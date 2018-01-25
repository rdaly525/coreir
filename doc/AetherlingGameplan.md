How my system will work:
1. Magma - how users will express their modules and combine them.
2. Pycoreir - how I will get my coreIR modules to appear like regular magma ones. Through pycoreir, my map/reduce and other higher order modules will appear as regular magma modules but really are coreir modules 
3. CoreIR - how I will write my operators and transformations. They will be written here because Ross has already written lots of the infrastructure that I'll need for my IR, like passes and a representation of types that is easily manipulated by the passes. Also, by writing my code in CoreIR, other projects like the halide to coreIR work can take advantage of my work. The components of CoreIR that I'll use are: 
   1. Generators - how I will write the operators of Aetherling - These are functions that produces modules. I will write my map/reduce/other functional programming modules as generators. The generators can accept amount of parallelism and coreIR modules to parallelize as input parameters and produce modules with the desired amounts of parallelism. (note: some of these features were just added this week, I need to test them. Also, Lenny + Ross say 2 weeks for a CoreIR generator to be able to accept a magma module as input.) My implementation of mapN as a generator can be found at: https://github.com/David-Durst/coreir/blob/aetherling/src/libs/aetherlinglib.cpp
   1. Modules - the CoreIR instances that get mapped to circuits, like adders and counters
   1. Passes - how I will write my transformations and introduce buffers. Passes transform generators into modules and modules into other modules. This is where I will implement my space-time computations and buffer size computations. The users will create their functions (like apply a kernel) and call generators with those modules as parameters. The generators will indicate that the users want to parallelize the modules. I will then, through passes, transform the map/etc generators to get the right amount of parallelism and add in buffers between the various modules the match rates.
4. CoreIR C++ interpreter - how I will test my generators/modules/passes. See my first test here: https://github.com/David-Durst/coreir/blob/aetherling/tests/simulator/aetherlingSim.cpp . This test parallelizes multiplying an array of numbers by 2.



questions:
1. What is a buffer?
2. Do I create a place holder between all my modules that I replace on passes?
3. What are the space and time constraints on the CGRA chip? - need to talk to ross about this. sub qestions
   1. What is a unit of compute? ALU, LUT, etc. How do I abstract this into a general unit?
   1. How to map each of these units into a cost structure for the optimizer
   1. Are there physical constraints that make units of the same category not fungible? Does distance matter?