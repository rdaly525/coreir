#!/bin/sh
cp -r include release/.
cp -r bin release/.
cp -r lib release/.
#mkdir release
#cd release
#cmake -DCMAKE_BUILD_TYPE=release ..
#make -j8
#cd ..
cp -r release coreir-${TRAVIS_OS_NAME}
tar -zcvf coreir-${TRAVIS_OS_NAME}.tar.gz coreir-${TRAVIS_OS_NAME}
