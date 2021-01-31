import delegator
import pytest

def test_inline_example():
    cur_dir = 'tests/binary'
    in_file = 'examples/counters.json'
    res_file = f"{cur_dir}/build/canon_counters.json"
    gold_file = f"{cur_dir}/gold/canon_counters.json"
    res = delegator.run(f"bin/coreir -i {in_file} -p \"canonicalize; verify_canonical\" -o {res_file}")
    assert not res.return_code, res.out + res.err

