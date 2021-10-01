import subprocess


def test_slice_connectivity():
    # TODO: For some reason, I can only trigger the verifyconnectivity check
    # using the binary (i.e. using the standard unit test flow doesn't raise
    # the error we're trying to fix when updating verifyconnectivity to handle
    # slices properly)
    subprocess.run(
        'bin/coreir -i tests/binary/src/slice_connectivity.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib',
        shell=True, check=True
    )


def test_flatten_slice():
    subprocess.run(
        'bin/coreir -i tests/binary/src/flatten_slice.json'
        '           -p flatten'
        '           -o tests/binary/build/out.json',
        shell=True, check=True
    )

    subprocess.run('diff tests/binary/build/out.json  '
                   '     tests/binary/gold/flatten_slice.json',
                   shell=True, check=True)
