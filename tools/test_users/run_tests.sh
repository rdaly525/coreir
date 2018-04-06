#!/bin/bash

set -e

cd coreir
git checkout dev
git pull
make install -j 8
cd ..

cd pycoreir
git checkout dev
git pull
pytest
cd ..

cd magma
git checkout coreir-dev
git pull
pytest
cd ..

cd mantle
git checkout coreir-dev
git pull
pytest
cd ..
