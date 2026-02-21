#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
ASSISTANT_TOOLS="$REPO_ROOT/isabelle-assistant/src/AssistantTools.scala"
IQ_INTEGRATION="$REPO_ROOT/isabelle-assistant/src/IQIntegration.scala"

for source_file in "$ASSISTANT_TOOLS" "$IQ_INTEGRATION"; do
  if [[ ! -f "$source_file" ]]; then
    echo "ERROR: missing source file: $source_file"
    exit 1
  fi
done

if command -v rg >/dev/null 2>&1; then
  GREP_CMD=(rg -n)
  GREP_QUIET=(rg -q)
else
  GREP_CMD=(grep -n -E)
  GREP_QUIET=(grep -q -E)
fi

extract_method() {
  local source_file="$1"
  local method_name="$2"
  awk -v method="$method_name" '
    $0 ~ "^[[:space:]]*(private[[:space:]]+)?def[[:space:]]+" method "\\(" { in_block = 1 }
    in_block && $0 ~ "^[[:space:]]*(private[[:space:]]+)?def[[:space:]]+" &&
      $0 !~ "^[[:space:]]*(private[[:space:]]+)?def[[:space:]]+" method "\\(" { exit }
    in_block { print }
  ' "$source_file"
}

check_mcp_only_method() {
  local source_file="$1"
  local source_label="$2"
  local method_name="$3"
  local forbidden_regex="$4"
  local required_regex="$5"
  local body

  body="$(extract_method "$source_file" "$method_name")"

  if [[ -z "$body" ]]; then
    echo "ERROR: unable to locate method '$method_name' in $source_label"
    exit 1
  fi

  if printf '%s\n' "$body" | "${GREP_QUIET[@]}" "$forbidden_regex"; then
    echo "ERROR: layering violation in '$method_name' ($source_label): forbidden execution path."
    printf '%s\n' "$body" | "${GREP_CMD[@]}" "$forbidden_regex"
    exit 1
  fi

  if ! printf '%s\n' "$body" | "${GREP_QUIET[@]}" "$required_regex"; then
    echo "ERROR: '$method_name' in $source_label must execute through IQMcpClient."
    exit 1
  fi
}

assistant_tools_mcp_only_methods=(
  execFindTheorems
  execVerifyProof
  execRunSledgehammer
  execRunNitpick
  execRunQuickcheck
  execExecuteStep
  execTraceSimplifier
)

assistant_forbidden='IQIntegration\.(verifyProofAsync|runSledgehammerAsync|runFindTheoremsAsync|runQueryAsync|getCommandAtOffset)|Extended_Query_Operation'

for method in "${assistant_tools_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$ASSISTANT_TOOLS" \
    "AssistantTools.scala" \
    "$method" \
    "$assistant_forbidden" \
    'IQMcpClient'
done

iq_integration_mcp_only_methods=(
  verifyProofAsync
  executeStepAsync
  runFindTheoremsAsync
  runQueryAsync
  runSledgehammerAsync
)

iq_integration_forbidden='Extended_Query_Operation|PIDE\.editor|AssistantConstants\.IQ_OPERATION_(ISAR_EXPLORE|FIND_THEOREMS)'

for method in "${iq_integration_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$IQ_INTEGRATION" \
    "IQIntegration.scala" \
    "$method" \
    "$iq_integration_forbidden" \
    'IQMcpClient'
done

echo "Layering checks passed."
