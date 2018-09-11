#!/bin/bash

set -eux

cd coreir
git checkout dev
git pull
make install -j 8
cd ..

cd pycoreir
git checkout dev
git pull
py.test -s
cd libcoreir-python
PYTHONPATH=test make test
cd ..
cd ..

cd magma
git checkout coreir-dev
git pull
py.test -s
cd ..

cd mantle
git checkout coreir-dev
git pull
py.test --target coreir tests/test_coreir -s
py.test --target coreir tests/test_mantle
cd ..
