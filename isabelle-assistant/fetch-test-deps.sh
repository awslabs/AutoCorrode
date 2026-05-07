#!/bin/bash
# Download ScalaTest / ScalaCheck JARs for the Isabelle Assistant test suite.
# Uses the same SHA-1-verifying helpers as fetch-deps.sh so tampered
# mirrors or network-in-the-middle cannot silently swap test JARs.

set -e

SCRIPT_DIR="$(dirname "$0")"
TEST_LIB_DIR="$SCRIPT_DIR/lib/test"
BASE_URL="https://repo1.maven.org/maven2"

# shellcheck source=fetch-deps-lib.sh
. "$SCRIPT_DIR/fetch-deps-lib.sh"

mkdir -p "$TEST_LIB_DIR"

# Maven Central relative paths of every test JAR we need. Mirrors the list
# that used to live inline in the Makefile, but now fetched via the
# SHA-1-verifying pipeline.
TEST_JARS=(
    "org/scalatest/scalatest_3/3.2.17/scalatest_3-3.2.17.jar"
    "org/scalatest/scalatest-core_3/3.2.17/scalatest-core_3-3.2.17.jar"
    "org/scalatest/scalatest-funsuite_3/3.2.17/scalatest-funsuite_3-3.2.17.jar"
    "org/scalatest/scalatest-matchers-core_3/3.2.17/scalatest-matchers-core_3-3.2.17.jar"
    "org/scalatest/scalatest-shouldmatchers_3/3.2.17/scalatest-shouldmatchers_3-3.2.17.jar"
    "org/scalactic/scalactic_3/3.2.17/scalactic_3-3.2.17.jar"
    "org/scalatest/scalatest-compatible/3.2.17/scalatest-compatible-3.2.17.jar"
    "org/scalacheck/scalacheck_3/1.17.0/scalacheck_3-1.17.0.jar"
    "org/scalatestplus/scalacheck-1-17_3/3.2.17.0/scalacheck-1-17_3-3.2.17.0.jar"
)

echo "Downloading ScalaTest and ScalaCheck JARs (SHA-1 verified)..."

for path in "${TEST_JARS[@]}"; do
    filename=$(basename "$path")
    dest="${TEST_LIB_DIR}/${filename}"
    url="${BASE_URL}/${path}"
    fetch_and_verify "$url" "$dest" "$filename"
done

echo ""
echo "Done. Test JARs downloaded and verified to $TEST_LIB_DIR"
