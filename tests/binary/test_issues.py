import delegator


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


def test_name_clobber():
    # https://github.com/rdaly525/coreir/issues/954
    res = delegator.run(
        'coreir -i tests/binary/src/name_clobber.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib'
    )
    assert not res.return_code, res.out + res.err

    res = delegator.run('verilator --lint-only tests/binary/build/out.v')
    assert not res.return_code, res.out + res.err

