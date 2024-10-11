#!/usr/bin/env bash

source CONFIGURE

symexec=$SE_DIR"test/build/symexec"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <filepath>"
    exit 1
fi

cpp -C -P $1 gen.c

ASAN_OPTIONS="detect_leaks=0" \
$symexec \
  --goal-file="goal.v" \
  --proof-auto-file="proof_auto.v" \
  --proof-manual-file="proof_manual.v" \
  --strategy-file="DSLFileLists" \
  --no-logic-path \
  --input-file="gen.c"
