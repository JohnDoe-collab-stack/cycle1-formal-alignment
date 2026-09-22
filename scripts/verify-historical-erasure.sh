#!/usr/bin/env bash
# Run from any directory in a checkout with the repository-pinned Lean installed.
set -euo pipefail
cd "$(dirname "$0")/.."

log_dir="${HISTORICAL_ERASURE_LOG_DIR:-/tmp/historical-erasure-verification}"
mkdir -p "$log_dir" .lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure
printf 'Commit: %s\n' "$(git rev-parse HEAD)" | tee "$log_dir/version.log"
lake env lean --version | tee -a "$log_dir/version.log"

lake build 2>&1 | tee "$log_dir/build.log"
lake build AuditRegression 2>&1 | tee "$log_dir/audit-regression-build.log"

for module in Local Chain Amplification Regression; do
  source="ConstitutiveSearch/HistoricalErasure/$module.lean"
  test -s "$source" || { echo "Required module missing: $source" >&2; exit 1; }
  lake env lean \
    -o ".lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure/$module.olean" \
    -c "$log_dir/$module.c" "$source" 2>&1 | tee "$log_dir/$module.log"
  if grep -E 'depends on axioms:|sorryAx|error:' "$log_dir/$module.log"; then
    echo "Compilation or axiom audit failed: $module" >&2
    exit 1
  fi
  grep -q 'does not depend on any axioms' "$log_dir/$module.log"
  test -s ".lake/build/lib/lean/ConstitutiveSearch/HistoricalErasure/$module.olean"
  test -s "$log_dir/$module.c"
done

lake env lean --run ConstitutiveSearch/HistoricalErasure/Regression.lean \
  2>&1 | tee "$log_dir/execution.log"
grep -q '^HISTORICAL_ERASURE_REGRESSIONS_PASSED$' "$log_dir/execution.log"

bash scripts/verify-axiom-audits.sh 2>&1 | tee "$log_dir/constructive-audit.log"
bash scripts/verify-manifest.sh 2>&1 | tee "$log_dir/manifest.log"
git diff --check
printf 'HISTORICAL_ERASURE_VERIFIED commit=%s\n' "$(git rev-parse HEAD)"
