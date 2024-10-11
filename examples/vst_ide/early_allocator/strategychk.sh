#!/usr/bin/env bash

source CONFIGURE

strategychk=$SE_DIR"test/build/StrategyCheck"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <filepath>"
    exit 1
fi

ASAN_OPTIONS="detect_leaks=0" \
$strategychk \
  --strategy-folder-path=. \
  --input-file=$1
