#!/usr/bin/env bash
# Setup Isabelle 2025-2 on a remote Ubuntu host (aarch64 or x86_64).
# Usage: setup_ubuntu.sh user@host [install_dir] [64|32] [skip_build]
set -euo pipefail

REMOTE="${1:?Usage: $0 user@host [install_dir] [64|32] [skip_build]}"
INSTALL_DIR="${2:-$HOME/Isabelle2025-2}"
BITS="${3:-64}"
SKIP_BUILD="${4:-}"

# Detect remote architecture and pick the right tarball
REMOTE_ARCH=$(ssh "$REMOTE" uname -m)
case "$REMOTE_ARCH" in
  aarch64)
    URL="https://isabelle.in.tum.de/dist/Isabelle2025-2_linux_arm.tar.gz"
    TARBALL="Isabelle2025-2_linux_arm.tar.gz"
    ;;
  x86_64)
    URL="https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz"
    TARBALL="Isabelle2025-2_linux.tar.gz"
    ;;
  *)
    echo "Unsupported architecture: $REMOTE_ARCH" >&2; exit 1
    ;;
esac

echo "=== Setting up Isabelle on $REMOTE ($REMOTE_ARCH, ${BITS}-bit) ==="

ssh "$REMOTE" bash -s "$URL" "$TARBALL" "$INSTALL_DIR" "$BITS" "$SKIP_BUILD" <<'REMOTE_SCRIPT'
set -euo pipefail
URL="$1"; TARBALL="$2"; INSTALL_DIR="$3"; BITS="$4"; SKIP_BUILD="${5:-}"
[[ "$INSTALL_DIR" = /* ]] || { echo "INSTALL_DIR must be an absolute path" >&2; exit 1; }

# fontconfig is needed by Isabelle's Java/Scala layer
sudo apt-get update -qq && sudo apt-get install -y -qq fontconfig

if [ -d "$INSTALL_DIR" ]; then
  echo "Already installed: ~/$INSTALL_DIR"
else
  echo "Downloading $URL ..."
  curl -fSL -o "/tmp/$TARBALL" "$URL"
  echo "Unpacking ..."
  tar xzf "/tmp/$TARBALL" -C /tmp
  rm "/tmp/$TARBALL"
  mkdir -p "$(dirname "$INSTALL_DIR")"
  mv "/tmp/Isabelle2025-2" "$INSTALL_DIR"
  # Disable SystemOnTPTP
  PREFS_DIR="$("$INSTALL_DIR"/bin/isabelle getenv -b ISABELLE_HOME_USER)/etc"
  mkdir -p "$PREFS_DIR"
  echo 'SystemOnTPTP = ""' >> "$PREFS_DIR/preferences"
  echo "Installed: $INSTALL_DIR"
fi

# AFP Word_Lib
AFP_URL="https://www.isa-afp.org/release/afp-Word_Lib-2026-02-06.tar.gz"
AFP_DIR="$HOME/.isabelle/Isabelle2025-2/AFP"
if [ -d "$AFP_DIR/Word_Lib" ]; then
  echo "AFP Word_Lib already installed"
else
  echo "Downloading AFP Word_Lib ..."
  mkdir -p "$AFP_DIR"
  curl -fSL "$AFP_URL" | tar xz -C "$AFP_DIR"
  "$INSTALL_DIR"/bin/isabelle components -u "$AFP_DIR/Word_Lib"
  echo "Registered AFP Word_Lib"
fi

ML_64_OPT=""
if [ "$BITS" = "64" ]; then ML_64_OPT="-o ML_system_64=true"; fi
if [ -z "$SKIP_BUILD" ]; then
  echo "Building Pure + HOL (${BITS}-bit) ..."
  "$INSTALL_DIR"/bin/isabelle build -b $ML_64_OPT HOL
  echo "Done."
else
  echo "Skipping heap build (--copy-from-local)"
fi
REMOTE_SCRIPT
