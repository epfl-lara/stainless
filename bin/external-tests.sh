#!/usr/bin/env bash

# Compile Stainless

echo "Compiling Stainless..."

sbt u:stage

# Publish Stainless local and save the version

echo "Publishing Stainless..."

STAINLESS_VERSION=$(sbt publishLocal | sed -n -r 's#^.*stainless-scalac-plugin_2.12.8/([^/]+)/poms.*$#\1#p')

echo "Published Stainless version is: $STAINLESS_VERSION"

# Create a directory for doing tests and move there

TEST_DIR="TMP_EXTERNAL_TESTS"

mkdir -p "$TEST_DIR"

bin/stainless-actors-tests.sh $TEST_DIR $STAINLESS_VERSION
bin/bolts-tests.sh $TEST_DIR

rm -rf "$TEST_DIR"
