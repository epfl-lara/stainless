#!/usr/bin/env bash
# ====
#  This script assembles the `stainless-scalac-standalone` subproject into
#  a fat jar and packages it into an archive that contains additional Z3
#  dependencies and a launcher script that makes said dependencies available
#  to the java process.
#  Currently only Linux (i.e. Z3's `ubuntu` binaries) and macOS are implemented.
# ====
set -e

STAINLESS_VERSION=$(git describe --abbrev=7 | sed 's/v//g')
if [[ $(git diff --stat) != '' ]]; then
  STAINLESS_VERSION="$STAINLESS_VERSION-SNAPSHOT"
fi

SCALA_VERSION="3.0.2"
Z3_VERSION="4.8.12"

SBT_PACKAGE="sbt stainless-scalac-standalone/assembly"
STAINLESS_JAR_PATH="./frontends/stainless-scalac-standalone/target/scala-$SCALA_VERSION/stainless-scalac-standalone-$STAINLESS_VERSION.jar"
# Note: though Stainless is compiled with 3.0.2, we use a 2.13 version of ScalaZ3 (which is binary compatible with Scala 3)
SCALAZ3_JAR_LINUX_PATH="./unmanaged/scalaz3-unix-64-2.13.jar"
SCALAZ3_JAR_MAC_PATH="./unmanaged/scalaz3-mac-64-2.13.jar"

Z3_GITHUB_URL="https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION"
Z3_LINUX_NAME="z3-$Z3_VERSION-x64-glibc-2.31.zip"
Z3_MAC_NAME="z3-$Z3_VERSION-x64-osx-10.15.7.zip"

LOG="./package-standalone.log"

# -----

function info {
  echo "$1 $(tput sgr 0)"
}
function okay {
  info "$(tput setaf 2)    Done."
  echo -e "-----\n" >> $LOG
}
function fail {
  info "$(tput setaf 1)   Failed. See log ($LOG) for details."
  exit 1
}

# -----

TMP_DIR=$(mktemp -d 2>/dev/null || mktemp -d -t "stainless-package-standalone")

STAINLESS_JAR_BASENAME=$(basename "$STAINLESS_JAR_PATH")

function check_tools {
  for tool in \
    wget \
    unzip \
    zip \
    ; do
    if ! which ${tool} > /dev/null; then
      echo "Missing required utility \"${tool}\"; please install it" >> $LOG
      fail
    fi
  done

  okay
}

function fetch_z3 {
  local PLAT="$1"
  local NAME="$2"
  local ZIPF="$TMP_DIR/$NAME"
  local TMPD="$TMP_DIR/$PLAT"
  info " - $PLAT"

  if [ -f "$ZIPF" ]; then
    info "    (ZIP already exists, skipping download step.)"
  else
    wget -O "$ZIPF" "$Z3_GITHUB_URL/$NAME" 2>> $LOG || fail
  fi
  (rm -r "$TMPD" 2>/dev/null || true) && mkdir "$TMPD" || fail
  unzip -d "$TMPD" "$ZIPF" >> $LOG || fail

  mkdir "$TMPD/z3" >> $LOG || fail
  for COPY_FILE in LICENSE.txt bin/z3; do
    cp "$TMPD/${NAME%.*}/$COPY_FILE" "$TMPD/z3" >> $LOG || fail
  done

  okay
}

function generate_launcher {
  local TARGET="$1"
  local SCALAZ3_JAR_BASENAME="$2"

  cat "bin/launcher.tmpl.sh" | \
    sed "s#{STAINLESS_JAR_BASENAME}#$STAINLESS_JAR_BASENAME#g" | \
    sed "s#{SCALAZ3_JAR_BASENAME}#$SCALAZ3_JAR_BASENAME#g" \
    > "$TARGET"
  chmod +x "$TARGET"
}

function package {
  local PLAT="$1"
  local SCALAZ3_JAR_PATH="$2"
  local SCALAZ3_JAR_BASENAME
  SCALAZ3_JAR_BASENAME=$(basename "$SCALAZ3_JAR_PATH")

  local TMPD="$TMP_DIR/$PLAT"
  info " - $PLAT"

  local ZIPF
  ZIPF="$(pwd)/${STAINLESS_JAR_BASENAME%.*}-$PLAT.zip"

  if [ -f "$ZIPF" ]; then
    rm "$ZIPF" || fail
    info "    (Removed old archive.)"
  fi

  generate_launcher "$TMPD/stainless" "$SCALAZ3_JAR_BASENAME" || fail

  local TGTLIBD="$TMPD/lib"
  mkdir "$TGTLIBD" >> $LOG || fail
  cp "$STAINLESS_JAR_PATH" "$TGTLIBD/$STAINLESS_JAR_BASENAME" >> $LOG || fail
  cp "$SCALAZ3_JAR_PATH" "$TGTLIBD/$SCALAZ3_JAR_BASENAME" >> $LOG || fail
  cp "stainless.conf.default" "$TMPD/stainless.conf" >> $LOG || fail

  cd "$TMPD" && \
    zip "$ZIPF" lib/** z3/** stainless stainless.conf >> $LOG && \
    cd - >/dev/null || fail
  info "    Created archive $ZIPF"

  okay
}

# -----

echo -e "Starting packaging version $STAINLESS_VERSION on $(date).\n-----\n" | tee -a $LOG

info "$(tput bold)[] Checking required tools..."
check_tools

info "$(tput bold)[] Assembling fat jar..."
if [ -f "$STAINLESS_JAR_PATH" ]; then
  info "  (JAR already exists, skipping sbt assembly step.)" && okay
else
  $SBT_PACKAGE >> $LOG && okay || fail
fi

info "$(tput bold)[] Downloading Z3 binaries..."
fetch_z3 "linux" $Z3_LINUX_NAME
fetch_z3 "mac" $Z3_MAC_NAME

info "$(tput bold)[] Packaging..."
package "linux" $SCALAZ3_JAR_LINUX_PATH
package "mac" $SCALAZ3_JAR_MAC_PATH

info "$(tput bold)[] Cleaning up..."
rm -r "$TMP_DIR" && okay

info "$(tput bold)Packaging successful."
