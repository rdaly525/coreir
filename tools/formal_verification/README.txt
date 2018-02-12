==============================================================
Equivalence Checking via Transition Relation Analysis (CoreIR)
==============================================================

This analysis performs an equivalence checking between two systems,
and it tries to find a counterexample to the following assumption:

((inputs_1 = inputs_2) and (outputs_1 = outputs_2) and (inputs_1' = inputs_2')) -> (outputs_1' = outputs_2')

where var and var' represent current and next variable in the
transition relation.

* Passes required to perform the analysis *

1. Given system_1.json and system_2.json, generate system_1.smt2 and system_2.smt2 using CoreIR:

   ./bin/coreir -i system_1.json -p 'flattentypes,flatten,verifyflattenedtypes' -o system_1.smt2
   ./bin/coreir -i system_2.json -p 'flattentypes,flatten,verifyflattenedtypes' -o system_2.smt2

   NOTE: system_1.json and system_2.json can represent the outcome of
         two different sets of CoreIR passes:

         ./bin/coreir -i examples/mux.json -o system_1.json
         ./bin/coreir -i examples/mux.json -p 'fold-constants,deletedeadinstances' -o system_2.json

2. Given system_1.smt2 and system_2.smt2, generate the SMT encoding of the equivalence check:

   python tools/formal_verification/equivalence_checking.py -if1 system_1.smt2 -if2 system_2.smt2 -i1 "in0,in1" -o1 "out" -i2 "in0,in1" -o2 "out" > equivalence.smt2

3. Run CVC4 solver on equivalence.smt2 to check actual equivalence (requires CVC4 in the path):

   bash tools/formal_verification/cvc4_check.sh equivalence.smt2

4. If the two systems are equivalent, step 3. should return "unsat",
   otherwise the solver will provide a state when input and output
   variables of system_1 and system_2 are equal in the current state
   (i.e., var_name<1> and var_name<2>) but they differ in the next
   state (i.e., var_name<1>_N and var_name<2>_N)


==============================================================
Future Work
==============================================================

Automatize the equivalence analysis using a single Python script
