import subprocess

def test_concat_example():
    subprocess.run('bin/coreir -i examples/concat.json    '
                   '       -o tests/binary/build/out.v',
                   shell=True, check=True)
    subprocess.run('diff tests/binary/build/out.v  '
                   '     tests/binary/gold/concat.v',
                   shell=True, check=True)
