#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
ASSISTANT_SRC="$REPO_ROOT/isabelle-assistant/src"
ASSISTANT_TOOLS="$REPO_ROOT/isabelle-assistant/src/AssistantTools.scala"
PROOF_OPS_HANDLER="$REPO_ROOT/isabelle-assistant/src/ProofOpsToolHandler.scala"
THEORY_NAV_HANDLER="$REPO_ROOT/isabelle-assistant/src/TheoryNavToolHandler.scala"
IQ_INTEGRATION="$REPO_ROOT/isabelle-assistant/src/IQIntegration.scala"
THEORY_BROWSER="$REPO_ROOT/isabelle-assistant/src/TheoryBrowserAction.scala"
MODE="strict"
INVENTORY_OUT=""

usage() {
  cat <<'EOF'
Usage: check_layering.sh [--mode strict|report] [--inventory-out <path>]

Modes:
  strict  Enforce MCP-only migrated method boundaries and zero forbidden assistant runtime touchpoints (default).
  report  Emit assistant runtime boundary report (forbidden touchpoints only).
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

for source_file in "$ASSISTANT_TOOLS" "$PROOF_OPS_HANDLER" "$THEORY_NAV_HANDLER" "$IQ_INTEGRATION" "$THEORY_BROWSER"; do
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

# Read-only UI/context modules are permitted to perform local context probing
# for responsiveness (menu enablement, cursor/selection UX). Execution and
# semantic tool behavior remain guarded separately below.
ui_readonly_touchpoint_allowlist=(
  "isabelle-assistant/src/AssistantContextMenu.scala"
  "isabelle-assistant/src/MenuContext.scala"
  "isabelle-assistant/src/TargetParser.scala"
  "isabelle-assistant/src/ShowTypeAction.scala"
  "isabelle-assistant/src/ProofExtractor.scala"
  "isabelle-assistant/src/PrintContextAction.scala"
)

is_ui_readonly_allowlisted_path() {
  local path="$1"
  local allow
  for allow in "${ui_readonly_touchpoint_allowlist[@]}"; do
    if [[ "$path" == "$allow" ]]; then
      return 0
    fi
  done
  return 1
}

scan_runtime_touchpoints() {
  local mode="$1"
  local out_file="$2"
  : > "$out_file"

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
        if is_ui_readonly_allowlisted_path "$file"; then
          continue
        fi
        printf "%s\t%s\t%s\t%s\t%s\n" "$touchpoint" "$file" "$line" "$target" "$text" >> "$out_file"
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
        if is_ui_readonly_allowlisted_path "$file"; then
          continue
        fi
        printf "%s\t%s\t%s\t%s\t%s\n" "$touchpoint" "$file" "$line" "$target" "$text" >> "$out_file"
      done < <(grep -R -n -E "$regex" "$ASSISTANT_SRC" || true)
    fi
  done

  if [[ -s "$out_file" ]]; then
    sort -u "$out_file" -o "$out_file"
  fi

  if [[ "$mode" == "report" ]]; then
    echo "Layering runtime-boundary report (forbidden touchpoints):"
    if [[ ! -s "$out_file" ]]; then
      echo "  No forbidden runtime touchpoints detected in $ASSISTANT_SRC."
    else
      awk -F '\t' '{count[$1]++} END {for (k in count) printf "  - %s: %d\n", k, count[k]}' "$out_file" | sort
      echo
      printf "touchpoint\tfile\tline\ttarget_iq_capability\tsource\n"
      cat "$out_file"
    fi
  fi

  if [[ -n "$INVENTORY_OUT" ]]; then
    printf "touchpoint\tfile\tline\ttarget_iq_capability\tsource\n" > "$INVENTORY_OUT"
    if [[ -s "$out_file" ]]; then
      cat "$out_file" >> "$INVENTORY_OUT"
    fi
    echo "Wrote runtime touchpoint inventory to $INVENTORY_OUT"
  fi
}

enforce_zero_runtime_touchpoints() {
  local matches_file="$1"
  if [[ -s "$matches_file" ]]; then
    echo "ERROR: layering violation: forbidden assistant runtime touchpoints detected."
    echo "Semantic proof/file operations must live in iq capabilities."
    echo "Read-only UI/context introspection is allowed only in designated UI modules."
    echo
    printf "touchpoint\tfile\tline\ttarget_iq_capability\tsource\n"
    cat "$matches_file"
    exit 1
  fi
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

# Whole-file sweep for val-bindings that capture a forbidden symbol by
# reference. The MCP-only method-body check only scans text inside each
# method; this catches bypasses like `val f = IQIntegration.verifyProofAsync`
# at object/class level which could then be called from an MCP-only method
# via an indirection.
#
# We don't have a full Scala AST here — this regex-level sniff is a
# conservative gate. It deliberately errs on the side of forbidding any
# val/def/lazy val *definition* (as distinct from a call site) that
# mentions one of the banned symbols. The current codebase has zero such
# references, so any future occurrence is almost certainly a genuine
# bypass or an intentional escape hatch that should be reviewed.
#
# Multi-line handling: the file is first flattened through `tr '\n' ' '`
# into a single line so a binding like
#
#   val f =
#     IQIntegration.verifyProofAsync _
#
# still matches the forbidden regex. Single-line diagnostic is recovered
# by re-running `grep -n` on the original file for the forbidden symbol
# so the error message points at the real source line.
check_val_binding_bypasses() {
  local source_file="$1"
  local source_label="$2"
  local forbidden_regex="$3"

  # Combined pattern: `val|def|var` introducer, optional identifier, optional
  # type annotation, `=`, whitespace, then the forbidden symbol IMMEDIATELY
  # to the right of `=`. This tight boundary distinguishes a binding from an
  # ordinary method call: `val f = IQ.foo` matches, but `var x = ""` followed
  # by a later `IQ.foo(...)` call does not, even after newline flattening.
  #
  # The type-annotation segment allows generic brackets (`Option[Foo]`,
  # `Map[A, B]`, `Option[ Foo.bar.type ]`) by permitting any non-`=`,
  # non-bracket character inside `[...]` — including whitespace, commas,
  # and dots. `[^]=]` excludes `=` so we can't greedily swallow the
  # binding's own `=` if the regex engine decides to be creative.
  local combined_regex="(private[[:space:]]+|protected[[:space:]]+|implicit[[:space:]]+)*(lazy[[:space:]]+)?(val|def|var)[[:space:]]+[A-Za-z_][A-Za-z0-9_]*([[:space:]]*:[[:space:]]*[A-Za-z_][A-Za-z0-9_.]*(\\[[^]=]*\\])?)?[[:space:]]*=[[:space:]]+(${forbidden_regex})"

  local flattened
  flattened=$(tr '\n' ' ' < "$source_file")

  # Use `printf '%s\n' | grep` rather than `echo "$flattened" | grep` so that
  # (a) a flattened file starting with `-n`/`-e` can't be interpreted as an
  # echo flag, and (b) large flattened payloads survive shells where `echo`
  # buffers stdin awkwardly. `grep` on a here-string would be nicer, but
  # plain `/bin/sh` doesn't have `<<<`, and this script is portable to sh.
  if printf '%s\n' "$flattened" | grep -qE "$combined_regex"; then
    # Report on the original file so line numbers are meaningful.
    echo "ERROR: layering violation in $source_label: value binding that captures a forbidden runtime symbol by reference."
    if command -v rg >/dev/null 2>&1; then
      rg -n --no-heading --color never "(${forbidden_regex})" "$source_file" || true
    else
      grep -n -E "(${forbidden_regex})" "$source_file" || true
    fi
    echo "Either delete the binding, route through IQMcpClient, or (if this is a legitimate migration) update this guard explicitly."
    echo "(Matched against a newline-flattened copy of $source_label, so multi-line bindings cannot bypass this check.)"
    exit 1
  fi
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

# Dispatcher methods forward to other tool methods rather than calling
# IQMcpClient directly. They still must avoid the forbidden runtime paths
# (so bypasses can't hide behind a dispatch), but the required-pattern
# check is skipped because "dispatches to other execX" is the whole point.
#
# Keeping dispatchers in an explicit allowlist (rather than a comment that
# silently skips them) makes it impossible to demote a genuine MCP-only
# method to dispatcher-status without touching this file.
check_dispatcher_method() {
  local source_file="$1"
  local source_label="$2"
  local method_name="$3"
  local forbidden_regex="$4"
  local body

  body="$(extract_method "$source_file" "$method_name")"

  if [[ -z "$body" ]]; then
    echo "ERROR: unable to locate dispatcher method '$method_name' in $source_label"
    exit 1
  fi

  if printf '%s\n' "$body" | "${GREP_QUIET[@]}" "$forbidden_regex"; then
    echo "ERROR: layering violation in dispatcher '$method_name' ($source_label): forbidden execution path."
    printf '%s\n' "$body" | "${GREP_CMD[@]}" "$forbidden_regex"
    exit 1
  fi
}

run_strict_mcp_guards() {
assistant_tools_mcp_only_methods=(
  getGoalStateResult
  execGetProofContext
  execFindTheorems
  execGetType
  execGetCommandText
  execGetProofBlock
  execGetContextInfo
  execGetErrors
  execGetWarnings
  execEditTheory
  execGetEntities
  execCreateTheory
  execOpenTheory
)

assistant_forbidden='IQIntegration\.(verifyProofAsync|runSledgehammerAsync|runFindTheoremsAsync|runQueryAsync|getCommandAtOffset)|Extended_Query_Operation|GoalExtractor|PrintContextAction|ShowTypeAction|CommandExtractor|ProofExtractor|MenuContext\.findTheoryBuffer|jEdit\.getBufferManager'

for method in "${assistant_tools_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$ASSISTANT_TOOLS" \
    "AssistantTools.scala" \
    "$method" \
    "$assistant_forbidden" \
    'IQMcpClient|execExplore'
done

check_val_binding_bypasses "$ASSISTANT_TOOLS" "AssistantTools.scala" "$assistant_forbidden"

# ProofOpsToolHandler hosts the explore-driven proof-state tools that used
# to live in AssistantTools. Same layering rules apply.
proof_ops_mcp_only_methods=(
  execVerifyProof
  execRunSledgehammer
  execRunNitpick
  execRunQuickcheck
  execExecuteStep
  execTraceSimplifier
)

for method in "${proof_ops_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$PROOF_OPS_HANDLER" \
    "ProofOpsToolHandler.scala" \
    "$method" \
    "$assistant_forbidden" \
    'IQMcpClient|execExplore'
done

check_val_binding_bypasses "$PROOF_OPS_HANDLER" "ProofOpsToolHandler.scala" "$assistant_forbidden"

# TheoryNavToolHandler hosts the read-only theory-navigation tools that used
# to live in AssistantTools.
theory_nav_mcp_only_methods=(
  execReadTheory
  execListTheories
  execSearchInTheory
  execSearchAllTheories
  execGetDependencies
)

# Dispatcher methods: forbidden paths still blocked, but no direct
# IQMcpClient call is required because they delegate to siblings above.
theory_nav_dispatcher_methods=(
  execSearchTheories
)

for method in "${theory_nav_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$THEORY_NAV_HANDLER" \
    "TheoryNavToolHandler.scala" \
    "$method" \
    "$assistant_forbidden" \
    'IQMcpClient|execExplore'
done

for method in "${theory_nav_dispatcher_methods[@]}"; do
  check_dispatcher_method \
    "$THEORY_NAV_HANDLER" \
    "TheoryNavToolHandler.scala" \
    "$method" \
    "$assistant_forbidden"
done

check_val_binding_bypasses "$THEORY_NAV_HANDLER" "TheoryNavToolHandler.scala" "$assistant_forbidden"

theory_browser_mcp_only_methods=(
  theories
  read
  deps
  search
)

theory_browser_forbidden='MenuContext|jEdit\.getBufferManager|getText\(|getLength\(\)|split\("\\\\n"\)'

for method in "${theory_browser_mcp_only_methods[@]}"; do
  check_mcp_only_method \
    "$THEORY_BROWSER" \
    "TheoryBrowserAction.scala" \
    "$method" \
    "$theory_browser_forbidden" \
    'IQMcpClient'
done

# Note: MenuContext is a legitimate type reference in TheoryBrowserAction
# (it appears in method signatures). Restrict the val-binding bypass check
# to the truly forbidden runtime symbols here.
theory_browser_forbidden_bindings='jEdit\.getBufferManager|getLength\(\)'
check_val_binding_bypasses "$THEORY_BROWSER" "TheoryBrowserAction.scala" "$theory_browser_forbidden_bindings"

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

check_val_binding_bypasses "$IQ_INTEGRATION" "IQIntegration.scala" "$iq_integration_forbidden"
}

RUNTIME_TOUCHPOINTS_FILE="$(mktemp)"
trap 'rm -f "$RUNTIME_TOUCHPOINTS_FILE"' EXIT

scan_runtime_touchpoints "$MODE" "$RUNTIME_TOUCHPOINTS_FILE"

if [[ "$MODE" == "strict" ]]; then
  run_strict_mcp_guards
  enforce_zero_runtime_touchpoints "$RUNTIME_TOUCHPOINTS_FILE"
  echo "Layering checks passed."
else
  echo "Layering report completed (non-blocking)."
fi
