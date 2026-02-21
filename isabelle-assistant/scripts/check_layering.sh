#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
ASSISTANT_SRC="$REPO_ROOT/isabelle-assistant/src"
ASSISTANT_TOOLS="$REPO_ROOT/isabelle-assistant/src/AssistantTools.scala"
IQ_INTEGRATION="$REPO_ROOT/isabelle-assistant/src/IQIntegration.scala"
MODE="strict"
INVENTORY_OUT=""

usage() {
  cat <<'EOF'
Usage: check_layering.sh [--mode strict|report] [--inventory-out <path>]

Modes:
  strict  Enforce MCP-only migrated method boundaries (default).
  report  Emit non-blocking assistant runtime boundary debt report.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      shift
      if [[ $# -eq 0 ]]; then
        echo "ERROR: --mode requires an argument"
        exit 2
      fi
      MODE="$1"
      ;;
    --inventory-out)
      shift
      if [[ $# -eq 0 ]]; then
        echo "ERROR: --inventory-out requires an argument"
        exit 2
      fi
      INVENTORY_OUT="$1"
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "ERROR: unknown argument: $1"
      usage
      exit 2
      ;;
  esac
  shift
done

if [[ "$MODE" != "strict" && "$MODE" != "report" ]]; then
  echo "ERROR: invalid mode '$MODE' (expected 'strict' or 'report')"
  exit 2
fi

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

runtime_touchpoint_specs=(
  "extended_query_operation|Extended_Query_Operation|iq.explore_query"
  "pide_editor|PIDE\\.editor\\.[A-Za-z_]+\\(|iq.goal_and_query"
  "document_model_get_model|Document_Model\\.get_model\\(|iq.document_model_lookup"
  "document_model_snapshot|Document_Model\\.snapshot\\(|iq.document_snapshot"
  "snapshot_get_node|snapshot\\.get_node\\(|iq.command_lookup"
  "command_iterator|command_iterator\\(|iq.command_lookup"
)

scan_runtime_touchpoints() {
  local mode="$1"
  local tmp_matches
  tmp_matches="$(mktemp)"

  for spec in "${runtime_touchpoint_specs[@]}"; do
    local touchpoint regex target
    touchpoint="${spec%%|*}"
    regex="${spec#*|}"
    target="${regex#*|}"
    regex="${regex%%|*}"

    if command -v rg >/dev/null 2>&1; then
      while IFS=: read -r file line text; do
        [[ -z "${file:-}" ]] && continue
        file="${file#"$REPO_ROOT/"}"
        printf "%s\t%s\t%s\t%s\t%s\n" "$touchpoint" "$file" "$line" "$target" "$text" >> "$tmp_matches"
      done < <(rg -n --no-heading --color never "$regex" "$ASSISTANT_SRC" || true)
    else
      while IFS= read -r raw; do
        [[ -z "${raw:-}" ]] && continue
        local file rest line text
        file="${raw%%:*}"
        rest="${raw#*:}"
        line="${rest%%:*}"
        text="${rest#*:}"
        file="${file#"$REPO_ROOT/"}"
        printf "%s\t%s\t%s\t%s\t%s\n" "$touchpoint" "$file" "$line" "$target" "$text" >> "$tmp_matches"
      done < <(grep -R -n -E "$regex" "$ASSISTANT_SRC" || true)
    fi
  done

  if [[ -s "$tmp_matches" ]]; then
    sort -u "$tmp_matches" -o "$tmp_matches"
  fi

  if [[ "$mode" == "report" ]]; then
    echo "Layering debt report (non-blocking):"
    if [[ ! -s "$tmp_matches" ]]; then
      echo "  No runtime touchpoints detected in $ASSISTANT_SRC."
    else
      awk -F '\t' '{count[$1]++} END {for (k in count) printf "  - %s: %d\n", k, count[k]}' "$tmp_matches" | sort
      echo
      printf "touchpoint\tfile\tline\ttarget_iq_capability\tsource\n"
      cat "$tmp_matches"
    fi
  fi

  if [[ -n "$INVENTORY_OUT" ]]; then
    printf "touchpoint\tfile\tline\ttarget_iq_capability\tsource\n" > "$INVENTORY_OUT"
    if [[ -s "$tmp_matches" ]]; then
      cat "$tmp_matches" >> "$INVENTORY_OUT"
    fi
    echo "Wrote runtime touchpoint inventory to $INVENTORY_OUT"
  fi

  rm -f "$tmp_matches"
}

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

run_strict_mcp_guards() {
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
}

scan_runtime_touchpoints "$MODE"

if [[ "$MODE" == "strict" ]]; then
  run_strict_mcp_guards
  echo "Layering checks passed."
else
  echo "Layering report completed (non-blocking)."
fi
