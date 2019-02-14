import delegator
import os


def test_examples():
    
    for example in os.listdir('examples'):
        print("file",example)
        example_split = example.split('.')
        if len(example_split) !=2 or example_split[-1] != 'json':
            continue
    
        name = example_split[0]
        #Test input parsing
        res = delegator.run(f"bin/coreir -i examples/{example}")
        assert not res.return_code, res.out + res.err
        print(1)
        #Test serializing to json
        res = delegator.run(f"bin/coreir -i examples/{example} -o examples/build/{name}.json")
        assert not res.return_code, res.out + res.err
        print(2)

        #Test serializing to verilog
        res = delegator.run(f"bin/coreir -i examples/{example} -o examples/build/{name}.v")
        assert not res.return_code, res.out + res.err
        print(3)

        #Verify verilog syntax
        res = delegator.run(f"verilator --lint-only examples/build/{name}.v")
        assert not res.return_code, res.out + res.err
        print(4)

        ##Test serializing to verilog (inlined)
        #res = delegator.run(f"bin/coreir -i examples/{example} -o examples/build/{name}_inline.v --inline")
        #assert not res.return_code, res.out + res.err
        #print(5)

        ##Verify verilog syntax (inlined)
        #res = delegator.run(f"verilator --lint-only examples/build/{name}_inline.v")
        #assert not res.return_code, res.out + res.err
        #print(6)

      
     
