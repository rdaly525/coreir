import delegator
import os


def test_examples():
    
    for example in os.listdir('examples'):
        print("file",example)
        example_split = example.split('.')
        if len(example_split) !=2 or example_split[-1] != 'json':
            continue
    
        name = example_split[0]
        
        libs = "-l commonlib"
        #Test input parsing and serializing to json
        res = delegator.run(f"bin/coreir -i examples/{example} {libs} -o examples/build/{name}.json")
        assert not res.return_code, res.out + res.err
        
        #Test syntax of serialized json
        res = delegator.run(f"bin/coreir -i examples/build/{name}.json {libs}")
        assert not res.return_code, res.out + res.err
        
        #Test serializing to verilog
        res = delegator.run(f"bin/coreir -i examples/{example} {libs} -o examples/build/{name}.v")
        assert not res.return_code, res.out + res.err

        #Verify verilog syntax
        res = delegator.run(f"verilator --lint-only examples/build/{name}.v")
        assert not res.return_code, res.out + res.err

        #Test serializing to verilog (inlined)
        #TODO this hangs sometimes for some examples
        #res = delegator.run(f"bin/coreir -i examples/{example} -o examples/build/{name}_inline.v --inline")
        #assert not res.return_code, res.out + res.err

        #Verify verilog syntax (inlined)
        #res = delegator.run(f"verilator --lint-only examples/build/{name}_inline.v")
        #assert not res.return_code, res.out + res.err
