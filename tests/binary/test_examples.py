import delegator
import os
import pytest

examples = []
for example in os.listdir('examples'):
    example_split = example.split('.')
    if len(example_split) !=2 or example_split[-1] != 'json':
        continue
    examples.append(example)


@pytest.mark.parametrize("example", examples)
def test_examples(example):
    example_split = example.split('.')
    name = example_split[0]

    libs = "-l commonlib,float,float_CW"
    #Test input parsing and serializing to json
    res = delegator.run(f"bin/coreir -i examples/{example} {libs} -o examples/build/{name}.json")
    assert not res.return_code, res.out + res.err

    #Test syntax of serialized json
    res = delegator.run(f"bin/coreir -i examples/build/{name}.json {libs}")
    assert not res.return_code, res.out + res.err

    #Test serializing to verilog
    res = delegator.run(f"bin/coreir -i examples/{example} {libs} -p wireclocks-clk -o examples/build/{name}.sv")
    assert not res.return_code, res.out + res.err

    #Verify verilog syntax
    res = delegator.run(f"verilator --lint-only examples/build/{name}.sv")
    assert not res.return_code, res.out + res.err

    #Test serializing to verilog (inlined)
    #TODO this hangs sometimes for some examples
    #res = delegator.run(f"bin/coreir -i examples/{example} -o examples/build/{name}_inline.v --inline")
    #assert not res.return_code, res.out + res.err

    #Verify verilog syntax (inlined)
    #res = delegator.run(f"verilator --lint-only examples/build/{name}_inline.v")
    #assert not res.return_code, res.out + res.err


examples_no_verilog = []
for example in os.listdir('examples/no_verilog'):
    example_split = example.split('.')
    if len(example_split) !=2 or example_split[-1] != 'json':
        continue
    examples_no_verilog.append(example)

@pytest.mark.parametrize("example", examples_no_verilog)
def test_examples_noverilog(example):
        example_split = example.split('.')
        name = example_split[0]

        libs = "-l commonlib,float,float_CW"
        #Test input parsing and serializing to json
        res = delegator.run(f"bin/coreir -i examples/no_verilog/{example} {libs} -o examples/build/{name}.json")
        assert not res.return_code, res.out + res.err

        #Test syntax of serialized json
        res = delegator.run(f"bin/coreir -i examples/build/{name}.json {libs}")
        assert not res.return_code, res.out + res.err
