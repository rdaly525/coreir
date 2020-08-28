import delegator


def test_verilator_unused():
    res = delegator.run(
        'coreir -i tests/binary/src/verilator_compat.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib --verilator_compat'
    )
    print(res.out, res.err)
    assert not res.return_code, res.out + res.err

    res = delegator.run('verilator --lint-only -Wall -Wno-DECLFILENAME tests/binary/build/out.v')
    assert not res.return_code, res.out + res.err


def test_garnet_interconnect_name_clobber():
    res = delegator.run(
        'coreir -i tests/binary/src/Interconnect.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib'
    )
    assert not res.return_code, res.out + res.err

    res = delegator.run('verilator --lint-only tests/binary/build/out.v -I '
                        'tests/binary/stubs.v')
    assert not res.return_code, res.out + res.err

