#!/bin/bash
# v2 verification pipeline for one cut: run_orders2 13 -> orders_words 13 -> allwords 14 (K27)
cd /workspace/eml-hub/speedups/checks/recip
c=$1
TAG=v2 python3 run_orders2.py 13 $c > logs_v2/o2_13_$c.log 2>&1
python3 orders_words.py 13 $c > logs_v2/orders_words_13_$c.log 2>&1
if [ "$c" = principal ]; then while [ ! -f logs_v2/aw14_lower.done ]; do sleep 20; done; fi
python3 allwords.py 14 $c > logs_v2/allwords_14_$c.log 2>&1
touch logs_v2/aw14_$c.done
