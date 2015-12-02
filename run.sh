#!/usr/bin/env bash

# for debugging

RUN_STATIC=1
RUN_DYNAMIC=1

INPUT_PATTERN="../test/*.a"
cur=$(pwd)

if [ $RUN_STATIC = 1 ]; then
    cd static
    echo "running static..."

    for fname in $INPUT_PATTERN; do
        echo "===== K run => $fname ====="
        cat $fname
        echo ""

        krun --symbolic-execution --debug $fname

        echo "exit code => $?"
    done

    cd $cur
fi

if [ $RUN_DYNAMIC = 1 ]; then
    cd dynamic
    echo "running dynamic..."

    for fname in $INPUT_PATTERN; do
        echo "===== K run => $fname ====="
        cat $fname
        echo ""

        # krun --symbolic-execution -c VENV='.Map[e <- Real(<<5>>)]' --debug $fname
        krun -c VENV='.Map' --debug $fname

        echo ""
    done

    cd $cur
fi
