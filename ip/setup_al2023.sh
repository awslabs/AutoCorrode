#!/usr/bin/env bash
# Setup Isabelle 2025-2 on a remote Amazon Linux 2023 host (aarch64 or x86_64).
# Uses the Poly/ML binary shipped with Isabelle after verifying it runs locally.
# Usage: setup_al2023.sh user@host [install_dir] [64|32] [skip_build]
set -euo pipefail

REMOTE="${1:?Usage: $0 user@host [install_dir] [64|32] [skip_build]}"
INSTALL_DIR="${2:-$HOME/Isabelle2025-2}"
BITS="${3:-64}"
SKIP_BUILD="${4:-}"

REMOTE_ARCH=$(ssh "$REMOTE" uname -m)
case "$REMOTE_ARCH" in
  aarch64)
    URL="https://isabelle.in.tum.de/website-Isabelle2025-2/dist/Isabelle2025-2_linux_arm.tar.gz"
    TARBALL="Isabelle2025-2_linux_arm.tar.gz"
    ;;
  x86_64)
    URL="https://isabelle.in.tum.de/website-Isabelle2025-2/dist/Isabelle2025-2_linux.tar.gz"
    TARBALL="Isabelle2025-2_linux.tar.gz"
    ;;
  *)
    echo "Unsupported architecture: $REMOTE_ARCH" >&2
    exit 1
    ;;
esac

echo "=== Setting up Isabelle on $REMOTE (Amazon Linux 2023, $REMOTE_ARCH, ${BITS}-bit) ==="

ssh "$REMOTE" bash -s "$URL" "$TARBALL" "$INSTALL_DIR" "$BITS" "$SKIP_BUILD" <<'REMOTE_SCRIPT'
set -euo pipefail
URL="$1"; TARBALL="$2"; INSTALL_DIR="$3"; BITS="$4"; SKIP_BUILD="${5:-}"
[[ "$INSTALL_DIR" = /* ]] || { echo "INSTALL_DIR must be an absolute path" >&2; exit 1; }
[[ "$BITS" = "32" || "$BITS" = "64" ]] || {
  echo "BITS must be 32 or 64" >&2
  exit 1
}

source /etc/os-release
[[ "$ID" = "amzn" && "$VERSION_ID" = "2023" ]] || {
  echo "Expected Amazon Linux 2023, found $ID $VERSION_ID" >&2
  exit 1
}

# fontconfig is needed by Isabelle's Java/Scala layer.
sudo dnf install -y fontconfig

if [ -x "$INSTALL_DIR/bin/isabelle" ]; then
  echo "Already installed: $INSTALL_DIR"
elif [ -e "$INSTALL_DIR" ]; then
  echo "Install path exists but is not a valid Isabelle installation: $INSTALL_DIR" >&2
  exit 1
else
  if [ ! -f "/tmp/$TARBALL" ]; then
    echo "Downloading $URL ..."
    curl -fSL --retry 5 --retry-all-errors --retry-delay 5 \
      -o "/tmp/$TARBALL" "$URL"
  fi
  echo "Unpacking ..."
  TMP_DIR=$(mktemp -d /tmp/isabelle-setup.XXXXXX)
  trap 'rm -rf "$TMP_DIR"' EXIT
  tar xzf "/tmp/$TARBALL" -C "$TMP_DIR"
  mkdir -p "$(dirname "$INSTALL_DIR")"
  mv "$TMP_DIR/Isabelle2025-2" "$INSTALL_DIR"
  echo "Installed: $INSTALL_DIR"
fi

PREFS_DIR="$("$INSTALL_DIR"/bin/isabelle getenv -b ISABELLE_HOME_USER)/etc"
mkdir -p "$PREFS_DIR"
grep -qxF 'SystemOnTPTP = ""' "$PREFS_DIR/preferences" 2>/dev/null ||
  echo 'SystemOnTPTP = ""' >> "$PREFS_DIR/preferences"

BASE_PLATFORM=$("$INSTALL_DIR"/bin/isabelle getenv -b ISABELLE_PLATFORM64)
if [ "$BITS" = "32" ]; then
  BASE_PLATFORM=${BASE_PLATFORM/x86_64-/x86_64_32-}
  BASE_PLATFORM=${BASE_PLATFORM/arm64-/arm64_32-}
fi
POLY="$INSTALL_DIR/contrib/polyml-5.9.2-2/$BASE_PLATFORM/poly"

echo "Checking packaged Poly/ML on $(getconf GNU_LIBC_VERSION) ..."
if [ ! -x "$POLY" ] || ! "$POLY" --version </dev/null; then
  echo "Packaged Poly/ML is incompatible with this host: $POLY" >&2
  exit 1
fi

if [ -z "$SKIP_BUILD" ]; then
  ML_64_OPT=""
  if [ "$BITS" = "64" ]; then ML_64_OPT="-o ML_system_64=true"; fi

  # Remove pre-built system heaps so isabelle build writes to the user directory.
  rm -rf "$INSTALL_DIR/heaps"
  echo "Building Pure + HOL (${BITS}-bit) ..."
  "$INSTALL_DIR"/bin/isabelle build -b $ML_64_OPT HOL
else
  echo "Skipping heap build (--copy-from-local)"
fi

echo "=== Done ==="
REMOTE_SCRIPT
