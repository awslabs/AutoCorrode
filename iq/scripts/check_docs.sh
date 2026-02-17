#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

SERVER_FILE="$REPO_ROOT/iq/src/IQServer.scala"
IQ_README="$REPO_ROOT/iq/README.md"

tmp_server_tools="$(mktemp)"
tmp_readme_tools="$(mktemp)"
cleanup() {
  rm -f "$tmp_server_tools" "$tmp_readme_tools"
}
trap cleanup EXIT

awk '
  /val tools = List\(/ { in_tools = 1 }
  in_tools { print }
  /val result = Map\("tools" -> tools\)/ { in_tools = 0 }
' "$SERVER_FILE" \
  | sed -nE 's/.*"name"[[:space:]]*->[[:space:]]*"([^"]+)".*/\1/p' \
  | sort -u > "$tmp_server_tools"

awk '
  /^## MCP Tools$/ { in_tools = 1; next }
  /^## / && in_tools { in_tools = 0 }
  in_tools { print }
' "$IQ_README" \
  | sed -nE 's/^[[:space:]]*[0-9]+\.[[:space:]]+\*\*([^*]+)\*\*:.*/\1/p' \
  | sort -u > "$tmp_readme_tools"

if ! diff -u "$tmp_server_tools" "$tmp_readme_tools" >/dev/null; then
  echo "ERROR: iq/README.md MCP tool list does not match iq/src/IQServer.scala registry."
  echo "Server-only tools:"
  comm -23 "$tmp_server_tools" "$tmp_readme_tools" | sed 's/^/  - /'
  echo "README-only tools:"
  comm -13 "$tmp_server_tools" "$tmp_readme_tools" | sed 's/^/  - /'
  exit 1
fi

normalize_anchor() {
  printf "%s" "$1" \
    | tr '[:upper:]' '[:lower:]' \
    | sed -E 's/`//g; s/[^a-z0-9 _-]//g; s/[[:space:]_]+/-/g; s/-+/-/g; s/^-|-$//g'
}

has_anchor() {
  local file="$1"
  local anchor="$2"
  local heading
  while IFS= read -r heading; do
    if [[ "$(normalize_anchor "$heading")" == "$anchor" ]]; then
      return 0
    fi
  done < <(grep -E '^#{1,6}[[:space:]]+' "$file" | sed -E 's/^#{1,6}[[:space:]]+//')
  return 1
}

check_links_in_file() {
  local file="$1"
  local failed=0
  local match target link_path link_anchor resolved target_anchor

  while IFS= read -r match; do
    target="${match#*](}"
    target="${target%)}"
    target="${target%% \"*}"
    target="${target#<}"
    target="${target%>}"

    [[ -z "$target" ]] && continue
    [[ "$target" == http://* ]] && continue
    [[ "$target" == https://* ]] && continue
    [[ "$target" == mailto:* ]] && continue

    link_path="$target"
    link_anchor=""
    if [[ "$target" == *"#"* ]]; then
      link_path="${target%%#*}"
      link_anchor="${target#*#}"
    fi

    if [[ -z "$link_path" ]]; then
      resolved="$file"
    elif [[ "$link_path" == /* ]]; then
      resolved="$link_path"
    else
      resolved="$(cd "$(dirname "$file")" && pwd)/$link_path"
    fi

    if [[ ! -e "$resolved" ]]; then
      echo "ERROR: Broken link in $file -> $target (missing file: $resolved)"
      failed=1
      continue
    fi

    if [[ -n "$link_anchor" && "$resolved" == *.md ]]; then
      target_anchor="$(normalize_anchor "$link_anchor")"
      if ! has_anchor "$resolved" "$target_anchor"; then
        echo "ERROR: Broken anchor in $file -> $target (missing anchor: #$link_anchor)"
        failed=1
      fi
    fi
  done < <(grep -oE '\[[^][]+\]\([^)]*\)' "$file")

  return "$failed"
}

DOC_FILES=(
  "$REPO_ROOT/iq/README.md"
  "$REPO_ROOT/isabelle-assistant/README.md"
  "$REPO_ROOT/isabelle-assistant/CONTRIBUTING.md"
)

for doc in "${DOC_FILES[@]}"; do
  check_links_in_file "$doc"
done

echo "Documentation checks passed."
