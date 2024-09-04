#!/usr/bin/env bash

# Run the complete CI pipeline

# Record the time to compute the total duration
TIME_BEFORE=$(date +%s)

BOLTS_ONLY=false
BUILD_ONLY=false
QUICK=false
SKIP_BUILD=false

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
    --build-only)
      BUILD_ONLY=true
      shift # past argument
      ;;
    --quick)
      QUICK=true
      shift # past argument
      ;;
    --skip-build)
      SKIP_BUILD=true
      shift # past argument
      ;;
    --bolts-only)
      BOLTS_ONLY=true
      shift # past argument
      ;;
    *)    # unknown option
      usage
      exit 1
      ;;
  esac
done

usage() {
 cat <<EOM
Usage: external-tests.sh [options]

  -h | -help         Print this message
  --skip-build       Do not build the project (saves time if the build is already up-to-date).
  --bolts-dir        Directory where bolts is located (default: clones from GitHub).
  --build-only       Only build the project, do not run tests.
  --quick            Skip the bolts tests.
  --bolts-only       Only run the bolts tests.

EOM
}

if [ "$SKIP_BUILD" = true ]; then
  echo "************** Skipping build **************"
else
  sbt universal:stage
  if [ $? -ne 0 ]; then
    echo "************** Failed to build the universal package **************"
    exit 1
  fi
  if [ "$BUILD_ONLY" = true ]; then
    echo "************** Build only done **************"
    exit 0
  fi
fi

if [ "$BOLTS_ONLY" = false ]; then
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

fi

if [ "$QUICK" = true ]; then
  echo "************** Quick mode, skipping bolts tests **************"
  exit 0
fi

# Run the Bolts benchmarks
# if BOLTS_DIR is set, pass it to the script
if [ -z "$BOLTS_DIR" ]; then
  bash bin/external-tests.sh --skip-build 
else
  bash bin/external-tests.sh --skip-build --bolts-dir $BOLTS_DIR
fi
if [ $? -ne 0 ]; then
  echo "Bolts benchmarks failed"
  exit 1
fi

TIME_AFTER=$(date +%s)
DURATION=$((TIME_AFTER - TIME_BEFORE))

echo ""
echo "********************************* CI PASSED! *********************************"

echo "Total time: $DURATION seconds"