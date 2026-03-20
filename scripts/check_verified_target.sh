#!/usr/bin/env bash
set -euo pipefail

ROOT_FILE="RLGeneralization.lean"
ROOT_OLEAN=".lake/build/lib/lean/RLGeneralization.olean"

if [[ ! -f "$ROOT_FILE" ]]; then
  echo "missing $ROOT_FILE" >&2
  exit 1
fi

MODULES=()
while IFS= read -r module; do
  [[ -n "$module" ]] || continue
  MODULES+=("$module")
done < <(sed -n 's/^import //p' "$ROOT_FILE")

if [[ ${#MODULES[@]} -eq 0 ]]; then
  echo "no imports found in $ROOT_FILE" >&2
  exit 1
fi

if [[ -d .lake/packages/SLT/.git ]]; then
  bash scripts/prepare_slt.sh
fi

FILES=()
for module in "${MODULES[@]}"; do
  path="$(printf '%s' "$module" | tr '.' '/').lean"
  if [[ ! -f "$path" ]]; then
    echo "imported module file missing: $path" >&2
    exit 1
  fi
  FILES+=("$path")
done

# Verify the root olean was produced by a prior build step.
if [[ ! -f "$ROOT_OLEAN" ]]; then
  echo "RLGeneralization.olean not found — run 'lake build --wfail RLGeneralization' first" >&2
  exit 1
fi

if grep -En ":\s*True\s*:=\s*by" "${FILES[@]}"; then
  echo "verified target contains a theorem/lemma with a literal True conclusion" >&2
  exit 1
fi

if grep -Fn "This file is NOT imported into the verified target." "${FILES[@]}"; then
  echo "verified target imports a file that self-identifies as excluded" >&2
  exit 1
fi

if grep -En "oracle strategy|vacuous placeholder|The theorem takes the bound as a hypothesis and returns it" "${FILES[@]}"; then
  echo "verified target contains draft/stub markers" >&2
  exit 1
fi

echo "verified target checks passed"
