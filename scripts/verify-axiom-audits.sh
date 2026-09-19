#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

failures=0

while IFS= read -r file; do
  begin_count="$(grep -F -c -- '/- AXIOM_AUDIT_BEGIN -/' "$file" || true)"
  end_count="$(grep -F -c -- '/- AXIOM_AUDIT_END -/' "$file" || true)"
  if [[ "$begin_count" -ne 1 || "$end_count" -ne 1 ]]; then
    printf 'Invalid axiom-audit block count: %s (begin=%s, end=%s)\n' \
      "$file" "$begin_count" "$end_count" >&2
    failures=1
  fi
done < <(git ls-files --cached --others --exclude-standard -- '*.lean')

forbidden_pattern='\b(noncomputable|sorry|Classical|propext|native_decide|unsafe)\b|\bQuot\.sound\b|implemented_by|^[[:space:]]*axiom\b'
if grep -En "$forbidden_pattern" $(git ls-files --cached --others --exclude-standard -- '*.lean'); then
  printf 'Forbidden Lean construct found.\n' >&2
  failures=1
fi

if [[ "$failures" -ne 0 ]]; then
  exit 1
fi

audit_output="$(mktemp)"
trap 'rm -f "$audit_output"' EXIT

set +e
lake build AuditRegression 2>&1 | tee "$audit_output"
build_status="${PIPESTATUS[0]}"
set -e

if [[ "$build_status" -ne 0 ]]; then
  exit "$build_status"
fi

if grep -Eq 'depends on axioms:|sorryAx' "$audit_output"; then
  printf 'Axiom dependency detected in audited declarations.\n' >&2
  exit 1
fi

printf 'All Lean audit blocks are present and axiom-free.\n'
