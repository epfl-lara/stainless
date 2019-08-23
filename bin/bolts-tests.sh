#!/usr/bin/env bash

set -e

TEST_DIR=$1
echo "Moving to $TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1

git clone https://github.com/epfl-lara/bolts

cd bolts || exit 1

bash ./run-tests.sh

cd ../.. || true

