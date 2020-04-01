import delegator
import pytest

@pytest.mark.parametrize("rst", [True, False])
def test_inline_example(rst):
    cur_dir = 'tests/binary'
    rst_suf = "_arst" if rst else ""
    in_file = f"{cur_dir}/src/mantle_reg{rst_suf}.json"
    res_file = f"{cur_dir}/build/mantle_reg_inline_single_instances{rst_suf}.json"
    gold_file = f"{cur_dir}/gold/mantle_reg_inline_single_instances{rst_suf}.json"
    res = delegator.run(f"bin/coreir -i {in_file} -l commonlib -p \"rungenerators; inline_single_instances\" -o {res_file}")
    assert not res.return_code, res.out + res.err
    res = delegator.run(f"diff {res_file} {gold_file}")
    assert not res.return_code, res.out + res.err


@pytest.mark.parametrize("rst", [True, False])
@pytest.mark.parametrize("suffix", ["json", "v"])
def test_clock_gate(rst, suffix):
    cur_dir = 'tests/binary'
    rst_suf = "_arst" if rst else ""
    in_file = f"{cur_dir}/src/mantle_reg{rst_suf}.json"
    res_file = f"{cur_dir}/build/mantle_reg_ce{rst_suf}.{suffix}"
    gold_file = f"{cur_dir}/gold/mantle_reg_ce{rst_suf}.{suffix}"
    res = delegator.run(f"bin/coreir -i {in_file} -l commonlib -p \"rungenerators; inline_single_instances; clock_gate; inline_single_instances\" -o {res_file}")
    assert not res.return_code, res.out + res.err
    res = delegator.run(f"diff {res_file} {gold_file}")
    assert not res.return_code, res.out + res.err

    #Test verilator linting if suffix is v
    if suffix == "v":
        res = delegator.run(f"verilator --lint-only {res_file}")
        assert not res.return_code, res.out + res.err
