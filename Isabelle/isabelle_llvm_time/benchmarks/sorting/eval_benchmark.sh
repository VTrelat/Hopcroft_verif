#!/bin/bash

# LOG="log/all-2020-10-09.log"
LOG="log/all_03_21.log"
LOG="log/all_03_21_notime.log"

rm -rf ~/tmp/data*.tex

# cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex
cat $LOG | ./__eval_benchmark.awk > ~/tmp/data.tex

gawk '$1=="@" { echo=($2=="introsort"); next }  echo {print} ' ~/tmp/data.tex  > ~/tmp/data_introsort.tex
# gawk '$1=="@" { echo=($2=="pdqsort"); next }  echo {print} ' ~/tmp/data.tex > ~/tmp/data_pdqsort.tex

cp ~/tmp/data_introsort.tex .
# cp ~/tmp/data_pdqsort.tex ../../papers/sorting/
