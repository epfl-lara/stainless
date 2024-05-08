#!/usr/bin/env bash

set -e

### The following section defines `realpath` to resolve symbolic links.
###
### Copyright (c) 2014 Michael Kropat
### Licensed under the terms of the MIT License (https://opensource.org/licenses/MIT)
### Original code at https://github.com/mkropat/sh-realpath

realpath() {
    canonicalize_path "$(resolve_symlinks "$1")"
}

resolve_symlinks() {
    _resolve_symlinks "$1"
}

_resolve_symlinks() {
    _assert_no_path_cycles "$@" || return

    local dir_context path
    path=$(readlink -- "$1")
    if [ $? -eq 0 ]; then
        dir_context=$(dirname -- "$1")
        _resolve_symlinks "$(_prepend_dir_context_if_necessary "$dir_context" "$path")" "$@"
    else
        printf '%s\n' "$1"
    fi
}

_prepend_dir_context_if_necessary() {
    if [ "$1" = . ]; then
        printf '%s\n' "$2"
    else
        _prepend_path_if_relative "$1" "$2"
    fi
}

_prepend_path_if_relative() {
    case "$2" in
        /* ) printf '%s\n' "$2" ;;
         * ) printf '%s\n' "$1/$2" ;;
    esac
}

_assert_no_path_cycles() {
    local target path

    target=$1
    shift

    for path in "$@"; do
        if [ "$path" = "$target" ]; then
            return 1
        fi
    done
}

canonicalize_path() {
    if [ -d "$1" ]; then
        _canonicalize_dir_path "$1"
    else
        _canonicalize_file_path "$1"
    fi
}

_canonicalize_dir_path() {
    (cd "$1" 2>/dev/null && pwd -P)
}

_canonicalize_file_path() {
    local dir file
    dir=$(dirname -- "$1")
    file=$(basename -- "$1")
    (cd "$dir" 2>/dev/null && printf '%s/%s\n' "$(pwd -P)" "$file")
}

### end of realpath code

usage() {
 cat <<EOM
Usage: external-tests.sh [options]

  -h | -help         Print this message
  --skip-build       Do not build Stainless (saves time if the build is already up-to-date).
EOM
}

SKIP_BUILD=false
while [[ $# -gt 0 ]]; do
  key="$1"

  case $key in
    -h|--help)
      usage
      exit 0
      ;;
    --skip-build)
      SKIP_BUILD=true
      shift # past argument
      ;;
    *)    # unknown option
      usage
      exit 1
      ;;
  esac
done

BIN_DIR=$( dirname "$( realpath "${BASH_SOURCE[0]}" )" )
BASE_DIR=$( dirname "$BIN_DIR" )

if command -v gsed >/dev/null 2>&1;
then
  SED="gsed"
else
  SED="sed"
fi

cd "$BASE_DIR" || exit 1

# Compile Stainless

if [[ "$SKIP_BUILD" = false ]]; then
  echo "Compiling Stainless..."
  sbt universal:stage

  # Publish Stainless local and save the version

  echo "Publishing Stainless..."

  STAINLESS_VERSION=$(sbt publishLocal | $SED -n -r 's#^.*stainless-dotty-plugin_3.3.3/([^/]+)/poms.*$#\1#p' | head -n1)

  echo "Published Stainless version is: $STAINLESS_VERSION"
else
  echo "Skipping build"
fi

export PATH="$BASE_DIR/frontends/scalac/target/universal/stage/bin:$PATH"
export PATH="$BASE_DIR/frontends/dotty/target/universal/stage/bin:$PATH"

# Create a directory for doing tests and move there

TEST_DIR="$BASE_DIR/.stainless-external-tests"
mkdir -p "$TEST_DIR"

# Stainless Actors are currently disabled: https://github.com/epfl-lara/stainless/issues/970
# "$BIN_DIR/stainless-actors-tests.sh" "$TEST_DIR" "$STAINLESS_VERSION"
echo "Running bolts test"
"$BIN_DIR/bolts-tests.sh" "$TEST_DIR" "stainless-dotty"