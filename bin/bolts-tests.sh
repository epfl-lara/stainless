#!/usr/bin/env bash

set -e

# --lite flag
if [[ "$1" == "--lite" ]]; then
  LITE_BOLTS=true
  shift # past argument
fi

# TEST_DIR should exist
TEST_DIR=$1
echo "Moving to $TEST_DIR"
# mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1


if [[ -d "bolts" ]]; then
  echo "Found bolts directory in $TEST_DIR!"
  cd bolts
  # We do not pull so that we can run the 
  # git pull || exit 1 
else
  git clone https://github.com/epfl-lara/bolts
  cd bolts || exit 1
fi

if [[ "$LITE_BOLTS" = true ]]; then
  echo "Running with the --lite-bolts flag, only running a subset of the tests"
  bash ./run-tests.sh --lite stainless-dotty
else
  bash ./run-tests.sh stainless-dotty
fi

cd ../.. || true
