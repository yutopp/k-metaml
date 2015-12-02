#!/usr/bin/env bash

# for debugging

BUILD_STATIC=1
BUILD_DYNAMIC=1

cur=$(pwd)

if [ $BUILD_STATIC = 1 ]; then
    cd static
    echo "compiling static..."

    kompile k-metaml-typing.k && echo "compiled static" || exit -1
    (kdoc --format pdf || exit -2) && mv k-metaml-typing.pdf ../.
    (kdoc --format latex || exit -2) && mv k-metaml-typing.tex ../.

    cd $cur
fi

if [ $BUILD_DYNAMIC = 1 ]; then
    cd dynamic
    echo "compiling dynamic..."

    kompile k-metaml-exec.k && echo "compiled dynamic" || exit -1
    (kdoc --format pdf || exit -2) && mv k-metaml-exec.pdf ../.
    (kdoc --format latex || exit -2) && mv k-metaml-exec.tex ../.

    cd $cur
fi
