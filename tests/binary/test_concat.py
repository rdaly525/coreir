import delegator

def test_concat_example():
    res = delegator.run('bin/coreir -i examples/concat.json    '
                        '       -o tests/binary/build/out.v')
    assert not res.return_code, res.out + res.err
    res = delegator.run('diff tests/binary/build/out.v  '
                        '     tests/binary/gold/concat.v')
    assert not res.return_code, res.out + res.err
