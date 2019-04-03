#!/bin/sh
#mkdir release
cd release
cmake -DCMAKE_BUILD_TYPE=release ..
make -j8
cd ..
#tar -zcvf coreir.tar.gz release
