#!/bin/bash
# Download AWS SDK v2 JARs for Bedrock Runtime. Shared SHA-1-verifying
# helpers live in fetch-deps-lib.sh so that fetch-test-deps (and any
# future fetcher) can reuse the same tamper-resistant pipeline.

set -e

VERSION="2.41.21"
BASE_URL="https://repo1.maven.org/maven2/software/amazon/awssdk"
SCRIPT_DIR="$(dirname "$0")"
LIB_DIR="$SCRIPT_DIR/lib"

# shellcheck source=fetch-deps-lib.sh
. "$SCRIPT_DIR/fetch-deps-lib.sh"

mkdir -p "$LIB_DIR"

JARS=(
    "bedrock"
    "bedrockruntime"
    "sdk-core"
    "aws-core"
    "regions"
    "auth"
    "http-client-spi"
    "json-utils"
    "protocol-core"
    "aws-json-protocol"
    "http-auth"
    "http-auth-aws"
    "apache-client"
    "url-connection-client"
    "profiles"
    "utils"
    "metrics-spi"
    "endpoints-spi"
    "annotations"
    "http-auth-spi"
    "identity-spi"
    "checksums"
    "checksums-spi"
    "third-party-jackson-core"
    "retries"
    "retries-spi"
)

# Additional third-party dependencies
THIRD_PARTY=(
    "org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar"
    "org/reactivestreams/reactive-streams/1.0.4/reactive-streams-1.0.4.jar"
    "com/samskivert/jmustache/1.16/jmustache-1.16.jar"
    "org/scilab/forge/jlatexmath/1.0.7/jlatexmath-1.0.7.jar"
    "org/scilab/forge/jlatexmath-font-greek/1.0.7/jlatexmath-font-greek-1.0.7.jar"
    "org/scilab/forge/jlatexmath-font-cyrillic/1.0.7/jlatexmath-font-cyrillic-1.0.7.jar"
)

echo "Downloading AWS SDK v2 JARs (version $VERSION)..."

for jar in "${JARS[@]}"; do
    url="${BASE_URL}/${jar}/${VERSION}/${jar}-${VERSION}.jar"
    dest="${LIB_DIR}/${jar}-${VERSION}.jar"
    fetch_and_verify "$url" "$dest" "$jar-$VERSION.jar"
done

echo "Downloading third-party dependencies..."
for path in "${THIRD_PARTY[@]}"; do
    filename=$(basename "$path")
    dest="${LIB_DIR}/${filename}"
    url="https://repo1.maven.org/maven2/${path}"
    fetch_and_verify "$url" "$dest" "$filename"
done

echo ""
echo "Done. JARs downloaded and verified to $LIB_DIR"
echo ""
ls -lh "$LIB_DIR"/*.jar | awk '{print $9, $5}'
