#!/usr/bin/env bash

set -e

TEST_DIR=$1
STAINLESS_VERSION=$2

echo "Moving to $TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1

echo "Verifying stainless-actors with Stainless version $STAINLESS_VERSION"

git clone https://github.com/epfl-lara/stainless-actors

cd stainless-actors || exit 1

sed -i "s/StainlessVersion = \".*\"/StainlessVersion = \"$STAINLESS_VERSION\"/" project/plugins.sbt || exit 1

ACTOR_EXAMPLES="counter leader-election kvs"

for ACTOR_EXAMPLE in $ACTOR_EXAMPLES; do

  echo "Running example $ACTOR_EXAMPLE..."
  sbt -mem 8192 "$ACTOR_EXAMPLE"/compile

  status=$?

  if [ $status -ne 0 ]
  then
    echo "Actor example $ACTOR_EXAMPLE failed."
    exit 1
  fi

done;

for ACTOR_EXAMPLE in $ACTOR_EXAMPLES; do

  echo "Running example $ACTOR_EXAMPLE with --type-checker..."
  sbt "$ACTOR_EXAMPLE"/compile

  status=$?

  if [ $status -ne 0 ]
  then
    echo "Actor example $ACTOR_EXAMPLE failed with --type-checker."
    exit 1
  fi

done;

cd ../.. || true

