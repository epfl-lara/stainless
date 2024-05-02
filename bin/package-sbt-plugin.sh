#!/usr/bin/env bash
set -e

STAINLESS_VERSION=$(git describe --abbrev=7 | sed 's/v//g')
if [[ $(git diff --stat) != '' ]]; then
  STAINLESS_VERSION="$STAINLESS_VERSION-SNAPSHOT"
fi

SCALA_VERSION="3.3.3"
SCALA_LIB_VERSION="2.13"
PUBLISHED_SBT_PLUGIN_DIR="$HOME/.ivy2/local/ch.epfl.lara/sbt-stainless/scala_2.12/sbt_1.0/$STAINLESS_VERSION"
PUBLISHED_LIB_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-library_$SCALA_LIB_VERSION/$STAINLESS_VERSION"
PUBLISHED_DOTTY_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-dotty-plugin_$SCALA_VERSION/$STAINLESS_VERSION"
PUBLISHED_SCALAC_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-scalac-plugin_$SCALA_VERSION/$STAINLESS_VERSION"

OUTPUT="./.stainless-package-sbt-plugin"
rm -rf "$OUTPUT" || true
mkdir -p "$OUTPUT"
LOG="$OUTPUT/package-sbt-plugin.log"

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

echo -e "Starting sbt-packaging version $STAINLESS_VERSION on $(date).\n-----\n" | tee -a $LOG

info "$(tput bold)[] Locally publishing artifacts..."
sbt publishLocal >> $LOG 2>&1 && okay || fail

info "$(tput bold)[] Preparing SBT plugin jar..."
OUT_SBT_JAR_DIR="$OUTPUT/project/lib"
mkdir -p "$OUT_SBT_JAR_DIR"
cp "$PUBLISHED_SBT_PLUGIN_DIR/jars/sbt-stainless.jar" "$OUT_SBT_JAR_DIR/sbt-stainless.jar"

info "$(tput bold)[] Preparing Stainless library jar..."
OUT_LIB_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-library_$SCALA_LIB_VERSION/$STAINLESS_VERSION"
mkdir -p "$OUT_LIB_DIR"
cp "$PUBLISHED_LIB_DIR/srcs/stainless-library_$SCALA_LIB_VERSION-sources.jar" "$OUT_LIB_DIR/stainless-library_$SCALA_LIB_VERSION-$STAINLESS_VERSION-sources.jar"
cp "$PUBLISHED_LIB_DIR/poms/stainless-library_$SCALA_LIB_VERSION.pom" "$OUT_LIB_DIR/stainless-library_$SCALA_LIB_VERSION-$STAINLESS_VERSION.pom"

info "$(tput bold)[] Preparing Dotty plugin jar..."
OUT_DOTTY_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-dotty-plugin_$SCALA_VERSION/$STAINLESS_VERSION"
mkdir -p "$OUT_DOTTY_DIR"
cp "$PUBLISHED_DOTTY_DIR/jars/stainless-dotty-plugin_$SCALA_VERSION.jar" "$OUT_DOTTY_DIR/stainless-dotty-plugin_$SCALA_VERSION-$STAINLESS_VERSION.jar"
cp "$PUBLISHED_DOTTY_DIR/poms/stainless-dotty-plugin_$SCALA_VERSION.pom" "$OUT_DOTTY_DIR/stainless-dotty-plugin_$SCALA_VERSION-$STAINLESS_VERSION.pom"

info "$(tput bold)[] Preparing Scalac plugin jar..."
OUT_SCALAC_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-scalac-plugin_$SCALA_VERSION/$STAINLESS_VERSION"
mkdir -p "$OUT_SCALAC_DIR"
cp "$PUBLISHED_SCALAC_DIR/jars/stainless-scalac-plugin_$SCALA_VERSION.jar" "$OUT_SCALAC_DIR/stainless-scalac-plugin_$SCALA_VERSION-$STAINLESS_VERSION.jar"
cp "$PUBLISHED_SCALAC_DIR/poms/stainless-scalac-plugin_$SCALA_VERSION.pom" "$OUT_SCALAC_DIR/stainless-scalac-plugin_$SCALA_VERSION-$STAINLESS_VERSION.pom"

info "$(tput bold)[] Creating archive..."
ARCHIVE="sbt-stainless"
cd "$OUTPUT" && zip -r "$ARCHIVE" project/ stainless/ >> /dev/null
cd .. && mv "$OUTPUT/$ARCHIVE.zip" "$ARCHIVE.zip"
info "    Created archive $ARCHIVE.zip"
