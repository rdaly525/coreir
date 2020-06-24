import delegator


def test_slice_connectivity():
    # TODO: For some reason, I can only trigger the verifyconnectivity check
    # using the binary (i.e. using the standard unit test flow doesn't raise
    # the error we're trying to fix when updating verifyconnectivity to handle
    # slices properly)
    res = delegator.run(
        'bin/coreir -i tests/binary/src/slice_connectivity.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib'
    )
    assert not res.return_code, res.out + res.err


def test_flatten_slice():
    res = delegator.run(
        'bin/coreir -i tests/binary/src/flatten_slice.json'
        '           -p flatten'
        '           -o tests/binary/build/out.json'
    )
    print(res.out)
    assert not res.return_code, res.err

    res = delegator.run('diff tests/binary/build/out.json  '
                        '     tests/binary/gold/flatten_slice.json')
    assert not res.return_code, res.out + res.err

