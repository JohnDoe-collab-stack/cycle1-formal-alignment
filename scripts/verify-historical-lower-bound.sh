#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
log_dir="${LOWER_BOUND_LOG_DIR:-$(mktemp -d /tmp/historical-lower-bound.XXXXXX)}"
mkdir -p "$log_dir" .lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure/LowerBound
commit="$(git rev-parse HEAD)"
dirty="$(git status --porcelain)"
if [[ -n "$dirty" && "${LOWER_BOUND_ALLOW_DIRTY:-0}" != 1 ]]; then
  printf 'A clean checkout is required for commit-confirmed verification.\n' >&2
  exit 1
fi
printf 'Commit: %s\n' "$commit" | tee "$log_dir/version.log"
lake env lean --version | tee -a "$log_dir/version.log"
sha256sum --check --strict LOWER_BOUND_MANIFEST.sha256 | tee "$log_dir/manifest.log"
HISTORICAL_ERASURE_LOG_DIR="$log_dir/original" bash scripts/verify-historical-erasure.sh \
  >"$log_dir/original-verification.log" 2>&1
for module in CoreFactorization QueryBound Regression; do
  source="ConstitutiveSearch/HistoricalErasure/LowerBound/$module.lean"
  lake env lean -o ".lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure/LowerBound/$module.olean" \
    -c "$log_dir/$module.c" "$source" 2>&1 | tee "$log_dir/$module.log"
  if grep -Eq 'depends on axioms:|sorryAx|error:' "$log_dir/$module.log"; then
    echo "Rejected: compilation/axiom audit of $module" >&2; exit 1
  fi
  expected="$(grep -c '^#print axioms ' "$source")"
  observed="$(grep -c 'does not depend on any axioms' "$log_dir/$module.log")"
  test "$observed" = "$expected"
  test -s ".lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure/LowerBound/$module.olean"
  test -s "$log_dir/$module.c"
done
python3 - "$log_dir" <<'PY_AUDIT'
from pathlib import Path
import re, sys
out = Path(sys.argv[1])
root = Path('ConstitutiveSearch/HistoricalErasure/LowerBound')
audit = ['import ConstitutiveSearch.HistoricalErasure.LowerBound.Regression\n']
names = []
for source in sorted(root.glob('*.lean')):
    stack = []
    for line in source.read_text().splitlines():
        text = line.strip()
        ns = re.match(r'^namespace (\S+)$', text)
        if ns:
            stack.append(ns.group(1)); continue
        if re.match(r'^end(?:\s+\S+)?$', text):
            if stack: stack.pop()
            continue
        text = re.sub(r'^@\[[^]]+\]\s*', '', text)
        found = re.match(r'^(?:def|theorem|structure|inductive|abbrev)\s+(\S+)', text)
        if found:
            name = '.'.join(stack + [found.group(1)])
            names.append(name)
            audit.append('#print axioms ' + name + '\n')
(out / 'IndependentAudit.lean').write_text(''.join(audit))
(out / 'audit-count.txt').write_text(str(len(names)))
c = (out / 'CoreFactorization.c').read_text()
m = re.search(r'LEAN_EXPORT [^\n]+_directNormalize[^\n;]*\([^\n;]*\)\s*\{', c)
if m is None: raise SystemExit('Direct function body not found')
p = c.index('{', m.start()); depth = 1; end = p + 1
while depth:
    if c[end] == '{': depth += 1
    elif c[end] == '}': depth -= 1
    end += 1
body = c[m.start():end]
if any(x in body for x in ('discover','executeFrom','buildStage','Stage_nextGuard')):
    raise SystemExit('Unexpected dynamic dependency in direct normalizer')
(out / 'direct-function.c.txt').write_text(body)
print('DIRECT_FUNCTION_HAS_NO_DYNAMIC_CALLS')
PY_AUDIT
lake env lean "$log_dir/IndependentAudit.lean" 2>&1 | tee "$log_dir/independent-audit.log"
if grep -Eq 'depends on axioms:|sorryAx|error:' "$log_dir/independent-audit.log"; then
  echo 'Independent audit failed' >&2; exit 1
fi
test "$(grep -c 'does not depend on any axioms' "$log_dir/independent-audit.log")" = "$(cat "$log_dir/audit-count.txt")"
lake env lean --run ConstitutiveSearch/HistoricalErasure/LowerBound/Regression.lean \
  2>&1 | tee "$log_dir/execution.log"
grep -q '^LOWER_BOUND_REGRESSIONS_PASSED$' "$log_dir/execution.log"
sha256sum --check --strict LOWER_BOUND_MANIFEST.sha256 >"$log_dir/manifest-after.log"
git diff --check
if [[ -z "$dirty" ]]; then
  test -z "$(git status --porcelain)"
  printf 'LOWER_BOUND_VERIFIED commit=%s\n' "$commit" | tee "$log_dir/result.log"
else
  printf 'LOWER_BOUND_WORKTREE_VERIFIED base=%s (not a commit-confirmed run)\n' "$commit" | tee "$log_dir/result.log"
fi
