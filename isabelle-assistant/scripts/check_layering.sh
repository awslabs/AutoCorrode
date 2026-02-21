#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
ASSISTANT_TOOLS="$REPO_ROOT/isabelle-assistant/src/AssistantTools.scala"

if [[ ! -f "$ASSISTANT_TOOLS" ]]; then
  echo "ERROR: missing source file: $ASSISTANT_TOOLS"
  exit 1
fi

if command -v rg >/dev/null 2>&1; then
  GREP_CMD=(rg -n)
  GREP_QUIET=(rg -q)
else
  GREP_CMD=(grep -n -E)
  GREP_QUIET=(grep -q -E)
fi

extract_method() {
  local method_name="$1"
  awk -v method="$method_name" '
    $0 ~ "^[[:space:]]*private def " method "\\(" { in_block = 1 }
    in_block && $0 ~ "^[[:space:]]*private def " &&
      $0 !~ "^[[:space:]]*private def " method "\\(" { exit }
    in_block { print }
  ' "$ASSISTANT_TOOLS"
}

check_mcp_only_method() {
  local method_name="$1"
  local body
  local forbidden_iq_regex='IQIntegration\.(verifyProofAsync|runSledgehammerAsync|runFindTheoremsAsync|runQueryAsync|getCommandAtOffset)'
  body="$(extract_method "$method_name")"

  if [[ -z "$body" ]]; then
    echo "ERROR: unable to locate method '$method_name' in AssistantTools.scala"
    exit 1
  fi

  if printf '%s\n' "$body" | "${GREP_QUIET[@]}" "$forbidden_iq_regex"; then
    echo "ERROR: layering violation in '$method_name': forbidden direct IQIntegration execution path."
    printf '%s\n' "$body" | "${GREP_CMD[@]}" "$forbidden_iq_regex"
    exit 1
  fi

  if printf '%s\n' "$body" | "${GREP_QUIET[@]}" 'Extended_Query_Operation'; then
    echo "ERROR: layering violation in '$method_name': direct Extended_Query_Operation usage is forbidden."
    printf '%s\n' "$body" | "${GREP_CMD[@]}" 'Extended_Query_Operation'
    exit 1
  fi

  if ! printf '%s\n' "$body" | "${GREP_QUIET[@]}" 'IQMcpClient'; then
    echo "ERROR: '$method_name' must execute through IQMcpClient."
    exit 1
  fi
}

mcp_only_methods=(
  execFindTheorems
  execVerifyProof
  execRunSledgehammer
  execRunNitpick
  execRunQuickcheck
  execExecuteStep
  execTraceSimplifier
)

for method in "${mcp_only_methods[@]}"; do
  check_mcp_only_method "$method"
done

echo "Layering checks passed."
