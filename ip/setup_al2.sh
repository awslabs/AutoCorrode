#!/bin/bash
# Setup Isabelle 2025-2 on a remote Amazon Linux 2 host (aarch64 or x86_64).
# Builds Poly/ML from source (no pre-built binary available for Amazon Linux 2).
# Usage: setup_al2.sh user@host [install_dir] [64|32] [skip_build]
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

echo "=== Setting up Isabelle on $REMOTE (Amazon Linux 2, $REMOTE_ARCH, ${BITS}-bit) ==="

ssh "$REMOTE" bash -s "$URL" "$TARBALL" "$INSTALL_DIR" "$BITS" "$SKIP_BUILD" <<'REMOTE_SCRIPT'
set -euo pipefail
URL="$1"; TARBALL="$2"; INSTALL_DIR="$3"; BITS="$4"; SKIP_BUILD="${5:-}"
[[ "$INSTALL_DIR" = /* ]] || { echo "INSTALL_DIR must be an absolute path" >&2; exit 1; }

ISABELLE_HOME="$INSTALL_DIR"
NPROC=$(nproc)

# Dependencies for building Poly/ML and running Isabelle
sudo yum install -y gcc gcc-c++ make gmp-devel fontconfig

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
  "$ISABELLE_HOME/bin/isabelle" components -u "$AFP_DIR/Word_Lib"
  echo "Registered AFP Word_Lib"
fi

if [ -z "$SKIP_BUILD" ]; then

POLYML_SRC=$ISABELLE_HOME/contrib/polyml-5.9.2-2/src
POLYML_DIR=$ISABELLE_HOME/contrib/polyml-5.9.2-2
ARCH=$(uname -m)

# Map uname -m to Isabelle platform names
case "$ARCH" in
  aarch64) PLAT64="arm64-linux"; PLAT32="arm64_32-linux" ;;
  x86_64)  PLAT64="x86_64-linux"; PLAT32="x86_64_32-linux" ;;
  *)       echo "Unsupported architecture: $ARCH" >&2; exit 1 ;;
esac

if [ "$BITS" = "32" ] || [ "$BITS" = "both" ]; then
  echo "=== Building Poly/ML 32-in-64 ($PLAT32) ==="
  cd "$POLYML_SRC"
  make distclean 2>/dev/null || true
  ./configure --prefix="$POLYML_SRC/target32" \
      --disable-shared --enable-intinf-as-int --with-gmp --enable-compact32bit
  make -j "$NPROC"
  make install
  mkdir -p "$POLYML_DIR/$PLAT32"
  cp target32/bin/poly "$POLYML_DIR/$PLAT32/poly"
  cp target32/bin/polyimport "$POLYML_DIR/$PLAT32/polyimport" 2>/dev/null || true
fi

if [ "$BITS" = "64" ] || [ "$BITS" = "both" ]; then
  echo "=== Building Poly/ML native 64-bit ($PLAT64) ==="
  cd "$POLYML_SRC"
  make distclean 2>/dev/null || true
  ./configure --prefix="$POLYML_SRC/target64" \
      --disable-shared --enable-intinf-as-int --with-gmp
  make -j "$NPROC"
  make install
  mkdir -p "$POLYML_DIR/$PLAT64"
  cp target64/bin/poly "$POLYML_DIR/$PLAT64/poly"
  cp target64/bin/polyimport "$POLYML_DIR/$PLAT64/polyimport" 2>/dev/null || true
fi

ML_64_OPT=""
if [ "$BITS" = "64" ]; then
  ML_64_OPT="-o ML_system_64=true"
fi

echo "=== Building heaps (Pure + HOL, ${BITS}-bit) ==="
"$ISABELLE_HOME/bin/isabelle" build -b $ML_64_OPT Pure
"$ISABELLE_HOME/bin/isabelle" build -b $ML_64_OPT HOL

else
  echo "Skipping Poly/ML build and heap build (--copy-from-local)"
fi

echo "=== Done ==="
REMOTE_SCRIPT
