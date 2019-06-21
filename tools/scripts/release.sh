#!/bin/sh
cp -r include release/.
cp -r bin release/.
cp -r lib release/.
#mkdir release
#cd release
#cmake -DCMAKE_BUILD_TYPE=release ..
#make -j8
#cd ..
tar -zcvf coreir.tar.gz release 
