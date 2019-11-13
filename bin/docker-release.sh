#!/usr/bin/env bash

set -e

if [ -z $1 ]; then
  echo "Usage: $0 STAINLESS_VERSION"
  exit 1
else
  STAINLESS_VERSION="$1"
fi

echo "Building Docker image for Stainless v$STAINLESS_VERSION..."
echo ""
echo "Press ENTER to continue, or Ctrl-C to abort..."

read tmp

echo "Building Docker image 'stainless:$STAINLESS_VERSION'..."
docker build --build-arg "STAINLESS_VERSION=$STAINLESS_VERSION" -t "stainless:$STAINLESS_VERSION" .

echo "Tagging Docker image 'stainless:latest'..."
docker tag stainless:$STAINLESS_VERSION stainless:latest
echo "Tagging Docker image 'epfllara/stainless:$STAINLESS_VERSION'..."
docker tag stainless:$STAINLESS_VERSION epfllara/stainless:$STAINLESS_VERSION
echo "Tagging Docker image 'epfllara/stainless:latest'..."
docker tag stainless:$STAINLESS_VERSION epfllara/stainless:latest

echo "Pushing Docker image 'epfllara/stainless:$STAINLESS_VERSION'..."
docker push epfllara/stainless:$STAINLESS_VERSION
echo "Pushing Docker image 'epfllara/stainless:latest'..."
docker push epfllara/stainless:latest

exit 0
