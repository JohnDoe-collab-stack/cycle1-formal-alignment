#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

echo '=== stale representation-boundary names ==='
grep -RIn \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  -E 'Cycle2|ReflectiveAlignment|reflective_alignment|alignement_reflexif|GlobalReflectiveClosure|noGlobalReflectiveClosure|exactCircularStatusRepresentation|circularDiagonalStatusExit|canonicalUnitCircularStatusView' \
  . || true

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
