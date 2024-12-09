#!/usr/bin/env bash
# ====
#  This script assembles the `stainless-scalac-standalone` and
#  `stainless-dotty-standalone` subprojects into two separate fat jars
#  and packages them into an archive that contains additional Z3
#  dependencies and a launcher script that makes said dependencies available
#  to the java process.
#  Currently, only the Linux & macOS version are shipped with ScalaZ3 (Windows must rely on smt-z3)
# ====
set -e

STAINLESS_VERSION=$(git describe --abbrev=7 | sed 's/v//g')
if [[ $(git diff --stat) != '' ]]; then
  STAINLESS_VERSION="$STAINLESS_VERSION-SNAPSHOT"
fi

SCALA_VERSION="3.5.2"
LIB_SCALA_VERSION="3.5.2"
LIB_SCALA_VERSION_JAR_NAME_PART=$(echo $LIB_SCALA_VERSION | cut -d '.' -f 1)
Z3_VERSION="4.12.2"
CVC5_VERSION="1.0.8"

SBT_PACKAGE_DOTTY="sbt stainless-dotty-standalone/assembly"
SBT_PACKAGE_LIB="sbt stainless-library/package stainless-library/packageSrc"
STAINLESS_DOTTY_JAR_PATH="./frontends/stainless-dotty-standalone/target/scala-$SCALA_VERSION/stainless-dotty-standalone-$STAINLESS_VERSION.jar"
STAINLESS_LIB_BIN_JAR_PATH="./frontends/library/target/scala-$LIB_SCALA_VERSION/stainless-library_$LIB_SCALA_VERSION_JAR_NAME_PART-$STAINLESS_VERSION.jar"
STAINLESS_LIB_SRC_JAR_PATH="./frontends/library/target/scala-$LIB_SCALA_VERSION/stainless-library_$LIB_SCALA_VERSION_JAR_NAME_PART-$STAINLESS_VERSION-sources.jar"
SCALAZ3_JAR_LINUX_PATH="./unmanaged/scalaz3-unix-64-3.jar"
SCALAZ3_JAR_MAC_X64_PATH="./unmanaged/scalaz3-mac-64-3.jar"

Z3_GITHUB_URL="https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION"
Z3_LINUX_NAME="z3-$Z3_VERSION-x64-glibc-2.31.zip"
Z3_MAC_ARM64_NAME="z3-$Z3_VERSION-arm64-osx-11.0.zip"
Z3_MAC_X64_NAME="z3-$Z3_VERSION-x64-osx-10.16.zip"
Z3_WIN_NAME="z3-$Z3_VERSION-x64-win.zip"

CVC5_GITHUB_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-$CVC5_VERSION"
CVC5_LICENSES_URL="https://raw.githubusercontent.com/cvc5/cvc5/main/licenses/"
CVC5_LICENSES=("minisat-LICENSE" "gpl-3.0.txt" "lgpl-3.0.txt")
CVC5_LINUX_NAME="cvc5-Linux"
CVC5_MAC_ARM64_NAME="cvc5-macOS-arm64"
CVC5_MAC_X64_NAME="cvc5-macOS"
CVC5_WIN_NAME="cvc5-Win64.exe"

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

function prepare_output_dir {
  for PLAT in "linux" "mac-arm64" "mac-x64" "win"; do
    TMPD="$TMP_DIR/$PLAT"
    (rm -r "$TMPD" 2>/dev/null || true) && mkdir -p "$TMPD" || fail
  done
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
  unzip -d "$TMPD" "$ZIPF" >> $LOG || fail

  mkdir -p "$TMPD/z3" >> $LOG || fail
  for COPY_FILE in LICENSE.txt "bin/$Z3_EXEC"; do
    cp "$TMPD/${NAME%.*}/$COPY_FILE" "$TMPD/z3" >> $LOG || fail
  done

  chmod +x "$TMPD/z3/$Z3_EXEC" >> $LOG || fail

  okay
}

function fetch_cvc5 {
  local PLAT="$1"
  local NAME="$2"
  local BINF="$TMP_DIR/$NAME"
  local TMPD="$TMP_DIR/$PLAT"
  local CVC5_EXEC
  info " - $PLAT"

  if [[ "$PLAT" = "win" ]]; then
    CVC5_EXEC="cvc5.exe"
  else
    CVC5_EXEC="cvc5"
  fi

  if [ -f "$BINF" ]; then
    info "    (Binary already exists, skipping download step.)"
  else
    wget -O "$BINF" "$CVC5_GITHUB_URL/$NAME" 2>> $LOG || fail
    for license in "${CVC5_LICENSES[@]}"; do
      wget -O "$TMP_DIR/cvc5_$license" "$CVC5_LICENSES_URL/$license" 2>> $LOG || fail
    done
  fi

  mkdir -p "$TMPD/cvc5" >> $LOG || fail
  mkdir -p "$TMPD/cvc5/licenses" >> $LOG || fail
  cp "$BINF" "$TMPD/cvc5/$CVC5_EXEC" >> $LOG || fail
  for license in "${CVC5_LICENSES[@]}"; do
    cp "$TMP_DIR/cvc5_$license" "$TMPD/cvc5/licenses/$license"
  done

  chmod +x "$TMPD/cvc5/$CVC5_EXEC" >> $LOG || fail

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
      > "$TMPD/stainless"
    chmod +x "$TMPD/stainless"
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
      > "$TMPD/stainless"
    chmod +x "$TMPD/stainless"
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

  local STAINLESS_SCRIPTS
  if [[ "$PLAT" = "win" ]]; then
    STAINLESS_SCRIPTS=("stainless.bat" "stainless")
  else
    STAINLESS_SCRIPTS=("stainless")
  fi

  cp "$STAINLESS_LIB_BIN_JAR_PATH" "$TMPD/lib/stainless-library.jar" >> $LOG || fail
  cp "$STAINLESS_LIB_SRC_JAR_PATH" "$TMPD/lib/stainless-library-sources.jar" >> $LOG || fail
  cp "bin/stainless-cli" "$TMPD/stainless-cli" >> $LOG || fail
  chmod +x "$TMPD/stainless-cli" >> $LOG || fail

  cd "$TMPD" && \
    zip "$ZIPF" lib/** z3/** cvc5/** "${STAINLESS_SCRIPTS[@]}" "stainless-cli" stainless.conf >> $LOG && \
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
if [[ -f "$STAINLESS_DOTTY_JAR_PATH" && -f "$STAINLESS_LIB_BIN_JAR_PATH" && -f "$STAINLESS_LIB_SRC_JAR_PATH" ]]; then
  info "  (JAR already exists, skipping sbt assembly step.)" && okay
else
  $SBT_PACKAGE_DOTTY | tee -a $LOG || fail
  ($SBT_PACKAGE_LIB | tee -a $LOG) && okay || fail
fi

prepare_output_dir

info "$(tput bold)[] Downloading Z3 binaries..."
fetch_z3 "linux" $Z3_LINUX_NAME
fetch_z3 "mac-arm64" $Z3_MAC_ARM64_NAME
fetch_z3 "mac-x64" $Z3_MAC_X64_NAME
fetch_z3 "win" $Z3_WIN_NAME

info "$(tput bold)[] Downloading cvc5 binaries..."
fetch_cvc5 "linux" $CVC5_LINUX_NAME
fetch_cvc5 "mac-arm64" $CVC5_MAC_ARM64_NAME
fetch_cvc5 "mac-x64" $CVC5_MAC_X64_NAME
fetch_cvc5 "win" $CVC5_WIN_NAME

info "$(tput bold)[] Packaging..."
package "linux" $STAINLESS_DOTTY_JAR_PATH $SCALAZ3_JAR_LINUX_PATH "dotty"
package "mac-arm64" $STAINLESS_DOTTY_JAR_PATH "" "dotty"
package "mac-x64" $STAINLESS_DOTTY_JAR_PATH $SCALAZ3_JAR_MAC_X64_PATH "dotty"
package "win" $STAINLESS_DOTTY_JAR_PATH "" "dotty"

info "$(tput bold)[] Cleaning up..."
# We only clean up the directories used for packaging; we leave the downloaded Z3/cvc5 binaries.
rm -r "$TMP_DIR/linux" "$TMP_DIR/mac-arm64" "$TMP_DIR/mac-x64" "$TMP_DIR/win" && okay

info "$(tput bold)Packaging successful."
