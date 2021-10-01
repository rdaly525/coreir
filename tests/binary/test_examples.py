import subprocess
import os
import pytest

examples = []
for example in os.listdir('examples'):
    example_split = example.split('.')
    if len(example_split) !=2 or example_split[-1] != 'json':
        continue
    examples.append(example)

@pytest.mark.parametrize("example",examples)
def test_examples(example):
        example_split = example.split('.')
        name = example_split[0]

        libs = "-l commonlib,float,float_CW"
        #Test input parsing and serializing to json
        subprocess.run(f"bin/coreir -i examples/{example} {libs} -o examples/build/{name}.json", shell=True, check=True)

        #Test syntax of serialized json
        subprocess.run(f"bin/coreir -i examples/build/{name}.json {libs}", shell=True, check=True)

        #Test serializing to verilog
        subprocess.run(f"bin/coreir -i examples/{example} {libs} -p wireclocks-clk -o examples/build/{name}.sv", shell=True, check=True)

        #Verify verilog syntax
        subprocess.run(f"verilator --lint-only examples/build/{name}.sv", shell=True, check=True)

        #Test serializing to verilog (inlined)
        #TODO this hangs sometimes for some examples
        #subprocess.run(f"bin/coreir -i examples/{example} -o examples/build/{name}_inline.v --inline", shell=True, check=True)

        #Verify verilog syntax (inlined)
        #subprocess.run(f"verilator --lint-only examples/build/{name}_inline.v", shell=True, check=True)
