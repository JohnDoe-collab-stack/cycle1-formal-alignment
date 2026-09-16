#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

# Temporary diagnostic for the experimental branch: print the exact hash of
# the new adversarial regression file before checking the manifest.
if [ -f Tests/MediatedTransitionCoherenceRegression.lean ]; then
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum Tests/MediatedTransitionCoherenceRegression.lean
  elif command -v shasum >/dev/null 2>&1; then
    shasum --algorithm 256 Tests/MediatedTransitionCoherenceRegression.lean
  fi
fi

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
