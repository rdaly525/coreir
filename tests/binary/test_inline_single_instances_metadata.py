import delegator


def test_inline_single_instances_metadata():
    res = delegator.run(
        'bin/coreir -i tests/binary/src/aoi_mux.json'
        '           -p inline_single_instances'
        '           -o tests/binary/build/out.json'
    )
    print(res.out)
    assert not res.return_code, res.err

    # Compare w/ orig source, should not have changed from
    # inline_single_instances
    res = delegator.run('diff tests/binary/build/out.json  '
                        '     tests/binary/src/aoi_mux.json')
    assert not res.return_code, res.out + res.err
