#!/usr/bin/env bash

# Run the complete CI pipeline

# Record the time to compute the total duration
TIME_BEFORE=$(date +%s)

BUILD_ONLY=false
SKIP_BOLTS=false
SKIP_BUILD=false
SKIP_SBT_PLUGIN=false
SKIP_TESTS=false

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
    --skip-bolts)
      SKIP_BOLTS=true
      shift # past argument
      ;;
    --skip-build)
      SKIP_BUILD=true
      shift # past argument
      ;;
    --skip-sbt-plugin)
      SKIP_SBT_PLUGIN=true
      shift # past argument
      ;;
    --skip-tests)
      SKIP_TESTS=true
      shift # past argument
      ;;
    --install-solvers)
      SOLVERS_DIR="$2"
      shift # past argument
      shift # past value
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

  -h | -help               Print this message
  --bolts-dir       <DIR>  Directory where bolts is located (default: clones from GitHub).
  --build-only             Only build the project, do not run tests.
  --skip-build             Do not build the project (saves time if the build is already up-to-date).
  --skip-bolts             Do not run the Bolts benchmarks.
  --skip-sbt-plugin        Do not run the sbt plugin tests.
  --skip-tests             Do not run the unit and integration tests.
  --install-solvers <DIR>  Install the solvers required for the tests (cvc5, CVC4, and z3) FOR LINUX.

EOM
}

# Download the solvers
if [ -n "$SOLVERS_DIR" ]; then
  TEMP_DIR="temp"
  mkdir -p "$SOLVERS_DIR"
  mkdir -p "$TEMP_DIR"
  # cvc5
  wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.0/cvc5-Linux-x86_64-static.zip -O "$TEMP_DIR/downloaded.zip"
  unzip "$TEMP_DIR/downloaded.zip" -d "$TEMP_DIR"
  CVC5_DIR=$(ls "$TEMP_DIR" | grep cvc5)
  mv "$TEMP_DIR/$CVC5_DIR/bin/cvc5" "$SOLVERS_DIR/cvc5"
  chmod +x "$SOLVERS_DIR/cvc5"
  rm -rf "$TEMP_DIR"
  
  # CVC4
  wget https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.8-x86_64-linux-opt -O "$SOLVERS_DIR/cvc4"
  chmod +x "$SOLVERS_DIR/cvc4"

  # z3
  mkdir -p "$TEMP_DIR"
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip -O "$TEMP_DIR/downloaded.zip"
  unzip "$TEMP_DIR/downloaded.zip" -d "$TEMP_DIR"
  Z3_DIR=$(ls "$TEMP_DIR" | grep z3)
  mv "$TEMP_DIR/$Z3_DIR/bin/z3" "$SOLVERS_DIR/z3"
  chmod +x "$SOLVERS_DIR/z3"
  rm -rf "$TEMP_DIR"

  echo "************** Solvers Installed **************"
  exit 0
fi

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

if [ "$SKIP_TESTS" = true ]; then
  echo "************** Skipping tests **************"
else
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

# Run the Bolts benchmarks
# if BOLTS_DIR is set, pass it to the script
if [ "$SKIP_BOLTS" = true ]; then
  echo "************** Skipping Bolts tests **************"
else
  if [ -z "$BOLTS_DIR" ]; then
    bash bin/external-tests.sh --skip-build 
  else
    bash bin/external-tests.sh --skip-build --bolts-dir $BOLTS_DIR
  fi
  if [ $? -ne 0 ]; then
    echo "Bolts benchmarks failed"
    exit 1
  fi
fi

# Run sbt scripted 
if [ "$SKIP_SBT_PLUGIN" = true ]; then
  echo "************** Skipping sbt plugin tests **************"
else
  sbt -batch scripted
  if [ $? -ne 0 ]; then
    echo "sbt scripted failed"
    exit 1
  fi
fi

# bash bin/build-slc-lib.sh
# if [ $? -ne 0 ]; then
#   echo "build-slc-lib.sh failed"
#   exit 1
# fi

TIME_AFTER=$(date +%s)
DURATION=$((TIME_AFTER - TIME_BEFORE))

echo ""
echo "********************************* CI PASSED! *********************************"

echo "Total time: $DURATION seconds"
