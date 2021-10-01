import subprocess


def test_inline_single_instances_metadata():
    subprocess.run(
        'bin/coreir -i tests/binary/src/aoi_mux.json'
        '           -p inline_single_instances'
        '           -o tests/binary/build/out.json',
        shell=True, check=True
    )

    # Compare w/ orig source, should not have changed from
    # inline_single_instances
    subprocess.run('diff tests/binary/build/out.json  '
                  '     tests/binary/src/aoi_mux.json',
                   shell=True, check=True)
