#!/usr/bin/env bash
# Verifies and runs the example projects with the given version of Stainless, which is resolved
# from Maven Central or from the local Ivy repository. To test the working tree:
#   sbt stainless-library/publishLocal stainless-dotty-plugin/publishLocal
#   examples/test.sh <the version sbt printed, e.g. 0.10.5-3-g1234567-SNAPSHOT>
# Needs scala (Scala CLI) and sbt on the PATH.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 <stainless version>" >&2
  exit 1
fi
VERSION="$1"

EXAMPLES_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
WORK_DIR=$(mktemp -d)
trap 'rm -rf "$WORK_DIR"' EXIT

# The examples refer to a released version: use the given one, in a copy
cp -r "$EXAMPLES_DIR/scala-cli" "$EXAMPLES_DIR/sbt" "$WORK_DIR"
sed -i.bak -E "s/(stainless-(library|dotty-plugin):)[^ ]+/\1$VERSION/" "$WORK_DIR/scala-cli/project.scala"
sed -i.bak -E "s/(val stainlessVersion = \")[^\"]+/\1$VERSION/" "$WORK_DIR/sbt/build.sbt"

# Fails unless the log has a verification summary without invalid or unknown verification
# conditions (which don't fail the compilation), and the output of the program.
check() {
  local name="$1" log="$2"
  if ! grep -q "invalid: 0 .*unknown: 0 " "$log"; then
    echo "$name: verification failed, see below" >&2
    cat "$log" >&2
    exit 1
  fi
  if ! grep -q "^15$" "$log"; then
    echo "$name: the program did not print 15, see below" >&2
    cat "$log" >&2
    exit 1
  fi
  echo "$name: verified and ran"
}

echo "Scala CLI example, with Stainless $VERSION..."
(cd "$WORK_DIR/scala-cli" && scala --power run --server=false . ) > "$WORK_DIR/scala-cli.log" 2>&1 || { cat "$WORK_DIR/scala-cli.log" >&2; exit 1; }
check "Scala CLI example" "$WORK_DIR/scala-cli.log"

echo "sbt example, with Stainless $VERSION..."
(cd "$WORK_DIR/sbt" && sbt -batch -no-colors compile run) > "$WORK_DIR/sbt.log" 2>&1 || { cat "$WORK_DIR/sbt.log" >&2; exit 1; }
check "sbt example" "$WORK_DIR/sbt.log"
