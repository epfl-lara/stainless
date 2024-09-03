#!/usr/bin/env bash

# Run the complete CI pipeline

# First parse the options
while [[ $# -gt 0 ]]; do
  key="$1"

  case $key in
    -h|--help)
      usage
      exit 0
      ;;
    --bolts-dir)
      BOLTS_DIR="$2"
      shift # past argument
      shift # past value
      ;;
    *)    # unknown option
      usage
      exit 1
      ;;
  esac
done

sbt universal:stage
if [ $? -ne 0 ]; then
  echo "************** Failed to build the universal package **************"
  exit 1
fi

# Run the tests
sbt -batch -Dtestsuite-parallelism=5 test
if [ $? -ne 0 ]; then
  echo "************** Unit tests failed **************"
  exit 1
fi

# Run the integration tests
sbt -batch -Dtestsuite-parallelism=3 -Dtestcase-parallelism=5 it:test
if [ $? -ne 0 ]; then
  echo "************** Integration tests failed **************"
  exit 1
fi

# Run the Bolts benchmarks

# if BOLTS_DIR is set, pass it to the script
if [ -z "$BOLTS_DIR" ]; then
  bash bin/external-tests.sh
else
  bash bin/external-tests.sh --bolts-dir $BOLTS_DIR
fi
if [ $? -ne 0 ]; then
  echo "Bolts benchmarks failed"
  exit 1
fi