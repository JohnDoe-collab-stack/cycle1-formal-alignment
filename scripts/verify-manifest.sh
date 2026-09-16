#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum \
    MediatedTransitionCoherence.lean \
    Cycle1/MediatedTransitionPasting.lean \
    Tests/MediatedTransitionPastingRegression.lean
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 \
    MediatedTransitionCoherence.lean \
    Cycle1/MediatedTransitionPasting.lean \
    Tests/MediatedTransitionPastingRegression.lean
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
