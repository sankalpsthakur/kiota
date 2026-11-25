#!/bin/bash
# check.sh <binary> <label>: run committed fixtures and r2adv exports, print wrong verdicts
B=$1; L=$2; fw=0; aw=0; fl=""; al=""
for f in tests/fixtures/*.accept.ndjson tests/fixtures/*.reject.ndjson; do
  case $f in *.accept.*) e=0;; *) e=1;; esac
  timeout 120 $B $f >/dev/null 2>&1; rc=$?
  if [ $rc != $e ]; then fw=$((fw+1)); fl="$fl $(basename $f .ndjson)=$rc"; fi
done
while IFS=$'\t' read f e; do
  timeout 120 $B r2adv/adv/$f >/dev/null 2>&1; rc=$?
  if [ $rc != $e ]; then aw=$((aw+1)); al="$al ${f%.ndjson}=$rc"; fi
done < r2adv/expected.tsv
echo "CHECK $L fixtures_wrong=$fw adv_wrong=$aw | fixtures:$fl | adv:$al"
