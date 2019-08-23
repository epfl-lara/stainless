#!/usr/bin/env bash

set -e

TEST_DIR=$1
echo "Moving to $TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1

git clone https://github.com/epfl-lara/bolts

cd bolts || exit 1

# The WIP folder is excluded because it contains work in progress which
# does not go through.

# The invalid folder is ignored as it contains examples which are invalid on
# purpose.
# TODO: test that they are indeed reported as invalid

STAINLESS_SCALAC="stainless-scalac --timeout=300 --vc-cache=false --fail-early"

echo "Running stainless-scalac on bolts..."
find . \
  -not \( -path ./WIP -prune \) \
  -not \( -path ./invalid -prune \) \
  -name "*.scala" \
  -exec $STAINLESS_SCALAC {} +
status=$?

if [ $status -ne 0 ]
then
  echo "$STAINLESS_SCALAC failed on bolts."
  exit 1
fi

# The `--type-checker` option does not support `forall` so all files containing
# `forall` are ignored.

echo "Running stainless-scalac --type-checker on bolts..."
find . \
  -not \( -path ./WIP -prune \)\
  -not \( -path ./invalid -prune \)\
  -not \( -path ./extended-gcd/ExtendedEuclidGCD.scala -prune \)\
  -not \( -path ./gcd/gcd.scala -prune \)\
  -not \( -path ./algorithms/sorting/QuickSortSize.scala -prune \)\
  -not \( -path ./algorithms/sorting/QuickSortSizeOccur.scala -prune \)\
  -name "*.scala" -exec $STAINLESS_SCALAC --type-checker {} +
status=$?

if [ $status -ne 0 ]
then
  echo "$STAINLESS_SCALAC --type-checker failed on bolts."
  exit 1
fi

cd ../.. || true

