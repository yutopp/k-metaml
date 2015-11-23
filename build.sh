#!/usr/bin/env bash

# for debugging

cur=$(pwd)

#kompile --backend java hoge.k && echo "compiled" && krun --symbolic-execution --pattern '<k> V:TypeTRI </k>' input_esc.a
#kompile hoge.k && echo "compiled" || exit -1

#cd static
#echo "static"
#
#kompile k-metaml-typing.k && echo "compiled static" || exit -1
##kdoc --debug --format html --doc-style=""|| exit -2
##kdoc --debug --format html || exit -2
#
#for fname in ../inputs/*.a; do
#    echo "===== K run => $fname ====="
#
#    krun --symbolic-execution --debug $fname
#
#    echo ""
#done
#
#cd $cur


cd dynamic
echo "dynamic"

kompile k-metaml-exec.k && echo "compiled dynamic" || exit -1
#kdoc --debug --format html --doc-style=""|| exit -2
#kdoc --debug --format html || exit -2

for fname in ../inputs/*.a; do
    echo "===== K run => $fname ====="

    krun --symbolic-execution -c VENV='.Map[e <- Real(<<5>>)]' --debug $fname

    echo ""
done

cd $cur
