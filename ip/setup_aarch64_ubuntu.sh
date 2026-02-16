#!/usr/bin/env bash
# Setup Isabelle 2025-2 on a remote aarch64 Ubuntu host.
# Usage: setup_aarch64_ubuntu.sh user@host [install_dir] [64|32] [skip_build]
set -euo pipefail

REMOTE="${1:?Usage: $0 user@host [install_dir] [64|32] [skip_build]}"
URL="https://isabelle.in.tum.de/dist/Isabelle2025-2_linux_arm.tar.gz"
TARBALL="Isabelle2025-2_linux_arm.tar.gz"
INSTALL_DIR="${2:-Isabelle2025-2}"
BITS="${3:-64}"
SKIP_BUILD="${4:-}"

echo "=== Setting up Isabelle on $REMOTE (${BITS}-bit) ==="

ssh "$REMOTE" bash -s "$URL" "$TARBALL" "$INSTALL_DIR" "$BITS" "$SKIP_BUILD" <<'REMOTE_SCRIPT'
set -euo pipefail
URL="$1"; TARBALL="$2"; INSTALL_DIR="$3"; BITS="$4"; SKIP_BUILD="$5"
cd ~

# fontconfig is needed by Isabelle's Java/Scala layer
sudo apt-get update -qq && sudo apt-get install -y -qq fontconfig

if [ -d "$INSTALL_DIR" ]; then
  echo "Already installed: ~/$INSTALL_DIR"
else
  echo "Downloading $URL ..."
  curl -fSL -o "$TARBALL" "$URL"
  echo "Unpacking ..."
  tar xzf "$TARBALL"
  rm "$TARBALL"
  echo "Installed: ~/$INSTALL_DIR"
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
  ~/"$INSTALL_DIR"/bin/isabelle components -u "$AFP_DIR/Word_Lib"
  echo "Registered AFP Word_Lib"
fi

ML_64_OPT=""
if [ "$BITS" = "64" ]; then ML_64_OPT="-o ML_system_64=true"; fi
if [ -z "$SKIP_BUILD" ]; then
  echo "Building Pure + HOL (${BITS}-bit) ..."
  ~/"$INSTALL_DIR"/bin/isabelle build -b $ML_64_OPT HOL
  echo "Done."
else
  echo "Skipping heap build (--copy-from-local)"
fi
REMOTE_SCRIPT
