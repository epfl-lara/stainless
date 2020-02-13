#!/usr/bin/env bash

set -e

TEST_DIR=$1
STAINLESS_VERSION=$2
SBT_ARGS="-batch -Dparallel=5 -Dsbt.color=always -Dsbt.supershell=false"

if command -v gsed >/dev/null 2>&1;
then
  SED="gsed"
else
  SED="sed"
fi

echo "Moving to $TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR" || exit 1

echo "Verifying stainless-actors with Stainless version $STAINLESS_VERSION"

git clone https://github.com/epfl-lara/stainless-actors

cd stainless-actors || exit 1

$SED -i "s#StainlessVersion = \".*\"#StainlessVersion = \"$STAINLESS_VERSION\"#" project/plugins.sbt || exit 1

ACTOR_EXAMPLES="counter leader-election kvs"

for ACTOR_EXAMPLE in $ACTOR_EXAMPLES; do

  echo "Running example $ACTOR_EXAMPLE..."
  sbt $SBT_ARGS "$ACTOR_EXAMPLE"/compile

  status=$?

  if [ $status -ne 0 ]
  then
    echo "Actor example $ACTOR_EXAMPLE failed."
    exit 1
  fi

done;

cd ../.. || true

