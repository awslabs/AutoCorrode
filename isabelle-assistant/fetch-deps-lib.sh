#!/bin/bash
# Shared helpers for Maven Central JAR fetching with SHA-1 verification.
#
# Each downloaded JAR is checksum-verified against the corresponding .sha1
# published by Maven Central. If the downloaded bytes do not match the
# published digest the script aborts and removes the bad file, so a
# compromised mirror or network-in-the-middle cannot silently swap in a
# different JAR.
#
# Usage: `source` this file from scripts that need `verify_sha1` and
# `fetch_and_verify`.

# Verify a downloaded JAR against its published Maven .sha1.
# Arguments: $1 = local jar path, $2 = remote .sha1 URL, $3 = friendly name
verify_sha1() {
    local jar="$1"
    local sha1_url="$2"
    local name="$3"

    local expected
    expected=$(curl -sfL "$sha1_url" | tr -d '[:space:]')
    if [ -z "$expected" ]; then
        echo "    FAIL: could not fetch expected .sha1 for $name from $sha1_url" >&2
        rm -f "$jar"
        return 1
    fi

    local actual
    if command -v shasum >/dev/null 2>&1; then
        actual=$(shasum -a 1 "$jar" | awk '{print $1}')
    elif command -v sha1sum >/dev/null 2>&1; then
        actual=$(sha1sum "$jar" | awk '{print $1}')
    else
        echo "    FAIL: neither shasum nor sha1sum is installed; cannot verify $name" >&2
        rm -f "$jar"
        return 1
    fi

    if [ "$actual" != "$expected" ]; then
        echo "    FAIL: $name checksum mismatch" >&2
        echo "      expected: $expected" >&2
        echo "      actual:   $actual" >&2
        rm -f "$jar"
        return 1
    fi
}

# Download-and-verify wrapper. Skips if the file already exists AND its
# checksum still matches (so a previously-verified cache is reused).
# Arguments: $1 = url, $2 = dest path, $3 = friendly name
fetch_and_verify() {
    local url="$1"
    local dest="$2"
    local name="$3"
    local sha1_url="${url}.sha1"

    if [ -f "$dest" ]; then
        # Re-verify cached file; if it's been tampered with since last run
        # we want to know.
        if verify_sha1 "$dest" "$sha1_url" "$name" 2>/dev/null; then
            echo "  $name already exists (verified)"
            return 0
        else
            echo "  $name exists but checksum failed; redownloading"
        fi
    fi

    echo "  Downloading $name..."
    curl -sfL "$url" -o "$dest"
    verify_sha1 "$dest" "$sha1_url" "$name"
}
