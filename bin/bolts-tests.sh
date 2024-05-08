#!/usr/bin/env bash

set -e

TEST_DIR=$1
echo "Moving to $TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1

if [[ -d "bolts" ]]; then
  cd bolts
  git pull || exit 1
else
  git clone https://github.com/epfl-lara/bolts
  cd bolts || exit 1
fi

bash ./run-tests.sh stainless-dotty

cd ../.. || true
