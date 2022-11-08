#!/usr/bin/env bash
set -e

STAINLESS_VERSION=$(git describe --abbrev=7 | sed 's/v//g')
if [[ $(git diff --stat) != '' ]]; then
  STAINLESS_VERSION="$STAINLESS_VERSION-SNAPSHOT"
fi

PUBLISHED_SBT_PLUGIN_DIR="$HOME/.ivy2/local/ch.epfl.lara/sbt-stainless/scala_2.12/sbt_1.0/$STAINLESS_VERSION"
PUBLISHED_LIB_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-library_2.13/$STAINLESS_VERSION"
PUBLISHED_DOTTY_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-dotty-plugin_3.2.0/$STAINLESS_VERSION"
PUBLISHED_SCALAC_DIR="$HOME/.ivy2/local/ch.epfl.lara/stainless-scalac-plugin_3.2.0/$STAINLESS_VERSION"

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
OUT_LIB_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-library_2.13/$STAINLESS_VERSION"
mkdir -p "$OUT_LIB_DIR"
cp "$PUBLISHED_LIB_DIR/srcs/stainless-library_2.13-sources.jar" "$OUT_LIB_DIR/stainless-library_2.13-$STAINLESS_VERSION-sources.jar"
cp "$PUBLISHED_LIB_DIR/poms/stainless-library_2.13.pom" "$OUT_LIB_DIR/stainless-library_2.13-$STAINLESS_VERSION-sources.pom"

info "$(tput bold)[] Preparing Dotty plugin jar..."
OUT_DOTTY_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-dotty-plugin_3.2.0/$STAINLESS_VERSION"
mkdir -p "$OUT_DOTTY_DIR"
cp "$PUBLISHED_DOTTY_DIR/jars/stainless-dotty-plugin_3.2.0.jar" "$OUT_DOTTY_DIR/stainless-dotty-plugin_3.2.0-$STAINLESS_VERSION.jar"
cp "$PUBLISHED_DOTTY_DIR/poms/stainless-dotty-plugin_3.2.0.pom" "$OUT_DOTTY_DIR/stainless-dotty-plugin_3.2.0-$STAINLESS_VERSION.pom"

info "$(tput bold)[] Preparing Scalac plugin jar..."
OUT_SCALAC_DIR="$OUTPUT/stainless/ch/epfl/lara/stainless-scalac-plugin_3.2.0/$STAINLESS_VERSION"
mkdir -p "$OUT_SCALAC_DIR"
cp "$PUBLISHED_SCALAC_DIR/jars/stainless-scalac-plugin_3.2.0.jar" "$OUT_SCALAC_DIR/stainless-scalac-plugin_3.2.0-$STAINLESS_VERSION.jar"
cp "$PUBLISHED_SCALAC_DIR/poms/stainless-scalac-plugin_3.2.0.pom" "$OUT_SCALAC_DIR/stainless-scalac-plugin_3.2.0-$STAINLESS_VERSION.pom"

info "$(tput bold)[] Creating archive..."
ARCHIVE="sbt-stainless"
cd "$OUTPUT" && zip -r "$ARCHIVE" project/ stainless/ >> /dev/null
cd .. && mv "$OUTPUT/$ARCHIVE.zip" "$ARCHIVE.zip"
info "    Created archive $ARCHIVE.zip"
