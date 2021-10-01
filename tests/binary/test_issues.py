import subprocess


def test_verilator_compat():
    subprocess.run(
        'coreir -i tests/binary/src/verilator_compat.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib --verilator_compat',
        shell=True, check=True
    )

    subprocess.run('verilator --lint-only -Wall -Wno-DECLFILENAME '
                   'tests/binary/build/out.v',
                   shell=True, check=True)


def test_garnet_interconnect_name_clobber():
    subprocess.run(
        'coreir -i tests/binary/src/Interconnect.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib',
        shell=True, check=True
    )

    subprocess.run('verilator --lint-only tests/binary/build/out.v -I '
                  'tests/binary/stubs.v',
                   shell=True, check=True)


def test_name_clobber():
    # https://github.com/rdaly525/coreir/issues/954
    subprocess.run(
        'coreir -i tests/binary/src/name_clobber.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib',
        shell=True, check=True
    )

    subprocess.run('verilator --lint-only tests/binary/build/out.v',
                   shell=True, check=True)


def test_953():
    subprocess.run(
        'coreir -i tests/binary/src/simple_mux.json'
        '           -o tests/binary/build/out.v'
        '           -l commonlib --inline',
        shell=True, check=True
    )

    subprocess.run('diff tests/binary/build/out.v  '
                   '     tests/binary/gold/simple_mux.v',
                   shell=True, check=True)
