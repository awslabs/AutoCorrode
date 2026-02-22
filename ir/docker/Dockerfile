FROM ubuntu:24.04

# Isabelle tarballs differ by architecture
ARG TARGETARCH
ARG ISABELLE_VERSION=Isabelle2025-2
ARG ISABELLE_BASE_URL=https://isabelle.in.tum.de/website-Isabelle2025-2/dist

RUN apt-get update -qq \
 && apt-get install -y -qq --no-install-recommends \
      curl ca-certificates python3 python3-pip \
      fontconfig fonts-dejavu-core rlwrap \
 && pip3 install --break-system-packages prompt_toolkit "mcp>=1.26" \
 && rm -rf /var/lib/apt/lists/*

# Download and install Isabelle for the target architecture
RUN set -e; \
    case "$TARGETARCH" in \
      amd64) TARBALL="${ISABELLE_VERSION}_linux.tar.gz" ;; \
      arm64) TARBALL="${ISABELLE_VERSION}_linux_arm.tar.gz" ;; \
      *) echo "Unsupported architecture: $TARGETARCH" && exit 1 ;; \
    esac; \
    curl -fsSL "${ISABELLE_BASE_URL}/${TARBALL}" | tar -xz -C /usr/local; \
    ln -s /usr/local/${ISABELLE_VERSION}/bin/isabelle /usr/local/bin/isabelle

ENV ISABELLE=/usr/local/${ISABELLE_VERSION}/bin/isabelle

# Copy repo
COPY . /opt/AutoCorrode

# Build HOL heap
RUN isabelle build -b HOL

EXPOSE 9148

CMD ["python3", "/opt/AutoCorrode/ir/repl.py", \
     "--session", "HOL", \
     "--host", "0.0.0.0", \
     "--isabelle", "/usr/local/Isabelle2025-2/bin/isabelle", \
     "--mcp", "--mcp-options", "--transport streamable-http --port 9148"]
