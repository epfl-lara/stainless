#!/usr/bin/env bash
# ====
#  This script assembles the `stainless-scalac-standalone` and
#  `stainless-dotty-standalone` subprojects into two separate fat jars
#  and packages them into an archive that contains additional Z3
#  dependencies and a launcher script that makes said dependencies available
#  to the java process.
#  Currently, only the Linux version is shipped with ScalaZ3 (macOS & Windows must rely on smt-z3)
# ====
set -e

STAINLESS_VERSION=$(git describe --abbrev=7 | sed 's/v//g')
if [[ $(git diff --stat) != '' ]]; then
  STAINLESS_VERSION="$STAINLESS_VERSION-SNAPSHOT"
fi

SCALA_VERSION="3.0.2"
Z3_VERSION="4.8.14"

SBT_PACKAGE_SCALAC="sbt stainless-scalac-standalone/assembly"
SBT_PACKAGE_DOTTY="sbt stainless-dotty-standalone/assembly"
STAINLESS_SCALAC_JAR_PATH="./frontends/stainless-scalac-standalone/target/scala-$SCALA_VERSION/stainless-scalac-standalone-$STAINLESS_VERSION.jar"
STAINLESS_DOTTY_JAR_PATH="./frontends/stainless-dotty-standalone/target/scala-$SCALA_VERSION/stainless-dotty-standalone-$STAINLESS_VERSION.jar"
# Note: though Stainless is compiled with 3.0.2, we use a 2.13 version of ScalaZ3 (which is binary compatible with Scala 3)
SCALAZ3_JAR_LINUX_PATH="./unmanaged/scalaz3-unix-64-2.13.jar"

Z3_GITHUB_URL="https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION"
Z3_LINUX_NAME="z3-$Z3_VERSION-x64-glibc-2.31.zip"
Z3_MAC_NAME="z3-$Z3_VERSION-x64-osx-10.16.zip"
Z3_WIN_NAME="z3-$Z3_VERSION-x64-win.zip"

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

# Directory of the script dir: https://stackoverflow.com/a/246128
SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
TMP_DIR="$SCRIPT_DIR/../.stainless-package-standalone"
mkdir -p "$TMP_DIR"

STAINLESS_SCALAC_JAR_BASENAME=$(basename "$STAINLESS_SCALAC_JAR_PATH")
STAINLESS_DOTTY_JAR_BASENAME=$(basename "$STAINLESS_DOTTY_JAR_PATH")

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
  local Z3_EXEC
  info " - $PLAT"

  if [[ "$PLAT" = "win" ]]; then
    Z3_EXEC="z3.exe"
  else
    Z3_EXEC="z3"
  fi

  if [ -f "$ZIPF" ]; then
    info "    (ZIP already exists, skipping download step.)"
  else
    wget -O "$ZIPF" "$Z3_GITHUB_URL/$NAME" 2>> $LOG || fail
  fi
  (rm -r "$TMPD" 2>/dev/null || true) && mkdir -p "$TMPD" || fail
  unzip -d "$TMPD" "$ZIPF" >> $LOG || fail

  mkdir -p "$TMPD/z3" >> $LOG || fail
  for COPY_FILE in LICENSE.txt "bin/$Z3_EXEC"; do
    cp "$TMPD/${NAME%.*}/$COPY_FILE" "$TMPD/z3" >> $LOG || fail
  done

  okay
}

function generate_launcher {
  local PLAT="$1"
  local TMPD="$2"
  local STAINLESS_JAR_BASENAME="$3"
  local SCALAZ3_JAR_BASENAME="$4"

  if [[ "$PLAT" = "win" ]]; then
    # For Windows, we generate two scripts, one .bat (native) and one .sh (executable with Cygwin).
    # The .bat version needs to have all '/' converted to '\'. We do this with this //\//\\ thing
    # (copied from https://unix.stackexchange.com/a/589316).
    # Since we do not ship ScalaZ3, we do not need to do replacing of SCALAZ3_JAR_BASENAME
    cat "bin/launcher-noscalaz3.tmpl.bat" | \
      sed "s#{STAINLESS_JAR_BASENAME}#${STAINLESS_JAR_BASENAME//\//\\}#g" \
      > "$TMPD/stainless.bat"
    chmod +x "$TMPD/stainless.bat"
    cat "bin/launcher-cygwin-noscalaz3.tmpl.sh" | \
      sed "s#{STAINLESS_JAR_BASENAME}#$STAINLESS_JAR_BASENAME#g" \
      > "$TMPD/stainless.sh"
    chmod +x "$TMPD/stainless.sh"
  else
    local SCRIPT_TMPLT_NAME
    if [[ "$SCALAZ3_JAR_BASENAME" = "" ]]; then
      SCRIPT_TMPLT_NAME="bin/launcher-noscalaz3.tmpl.sh"
    elif [[ "$PLAT" != "win" ]]; then
      SCRIPT_TMPLT_NAME="bin/launcher.tmpl.sh"
    fi

    cat "$SCRIPT_TMPLT_NAME" | \
      sed "s#{STAINLESS_JAR_BASENAME}#$STAINLESS_JAR_BASENAME#g" | \
      sed "s#{SCALAZ3_JAR_BASENAME}#$SCALAZ3_JAR_BASENAME#g" \
      > "$TMPD/stainless.sh"
    chmod +x "$TMPD/stainless.sh"
  fi
}

function package {
  local PLAT="$1"
  local STAINLESS_JAR_PATH="$2"
  local SCALAZ3_JAR_PATH="$3"
  local FRONTEND="$4"
  local STAINLESS_JAR_BASENAME=$(basename "$STAINLESS_JAR_PATH")
  local SCALAZ3_JAR_BASENAME=""
  if [[ "$SCALAZ3_JAR_PATH" != "" ]]; then
    SCALAZ3_JAR_BASENAME=$(basename "$SCALAZ3_JAR_PATH")
  fi

  local TMPD="$TMP_DIR/$PLAT"
  info " - $PLAT (for $FRONTEND)"

  local ZIPF
  ZIPF="$(pwd)/${STAINLESS_JAR_BASENAME%.*}-$PLAT.zip"

  if [ -f "$ZIPF" ]; then
    rm "$ZIPF" || fail
    info "    (Removed old $FRONTEND archive.)"
  fi

  generate_launcher "$PLAT" "$TMPD" "$STAINLESS_JAR_BASENAME" "$SCALAZ3_JAR_BASENAME" || fail

  local TGTLIBD="$TMPD/lib"
  mkdir -p "$TGTLIBD" >> $LOG || fail
  cp "$STAINLESS_JAR_PATH" "$TGTLIBD/$STAINLESS_JAR_BASENAME" >> $LOG || fail
  if [[ "$SCALAZ3_JAR_BASENAME" != "" ]]; then
    cp "$SCALAZ3_JAR_PATH" "$TGTLIBD/$SCALAZ3_JAR_BASENAME" >> $LOG || fail
  fi
  cp "stainless.conf.default" "$TMPD/stainless.conf" >> $LOG || fail

  local STAINLESS_SCRIPTSS
  if [[ "$PLAT" = "win" ]]; then
    STAINLESS_SCRIPTS=("stainless.bat" "stainless.sh")
  else
    STAINLESS_SCRIPTS=("stainless.sh")
  fi

  cd "$TMPD" && \
    zip "$ZIPF" lib/** z3/** "${STAINLESS_SCRIPTS[@]}" stainless.conf >> $LOG && \
    cd - >/dev/null || fail
  info "    Created $FRONTEND archive $ZIPF"

  rm "$TGTLIBD/$STAINLESS_JAR_BASENAME" >> $LOG || fail

  okay
}

# -----

echo -e "Starting packaging version $STAINLESS_VERSION on $(date).\n-----\n" | tee -a $LOG

info "$(tput bold)[] Checking required tools..."
check_tools

info "$(tput bold)[] Assembling fat jar..."
if [[ -f "$STAINLESS_SCALAC_JAR_PATH" && -f "$STAINLESS_DOTTY_JAR_PATH" ]]; then
  info "  (JAR already exists, skipping sbt assembly step.)" && okay
else
  $SBT_PACKAGE_SCALAC >> $LOG || fail
  $SBT_PACKAGE_DOTTY >> $LOG && okay || fail
fi

info "$(tput bold)[] Downloading Z3 binaries..."
fetch_z3 "linux" $Z3_LINUX_NAME
fetch_z3 "mac" $Z3_MAC_NAME
fetch_z3 "win" $Z3_WIN_NAME

info "$(tput bold)[] Packaging..."
package "linux" $STAINLESS_SCALAC_JAR_PATH $SCALAZ3_JAR_LINUX_PATH "scalac"
package "linux" $STAINLESS_DOTTY_JAR_PATH $SCALAZ3_JAR_LINUX_PATH "dotty"
package "mac" $STAINLESS_SCALAC_JAR_PATH "" "scalac"
package "mac" $STAINLESS_DOTTY_JAR_PATH "" "dotty"
package "win" $STAINLESS_SCALAC_JAR_PATH "" "scalac"
package "win" $STAINLESS_DOTTY_JAR_PATH "" "dotty"

info "$(tput bold)[] Cleaning up..."
# We only clean up the directories used for packaging; we leave the downloaded Z3 binaries.
rm -r "$TMP_DIR/linux" "$TMP_DIR/mac" "$TMP_DIR/win" && okay

info "$(tput bold)Packaging successful."
