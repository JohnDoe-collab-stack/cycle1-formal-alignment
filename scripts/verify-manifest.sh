#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

if command -v sha256sum >/dev/null 2>&1; then
  if ! verification_output="$(sha256sum --check --strict MANIFEST.sha256 2>&1)"; then
    printf '%s\n' "$verification_output"
    printf '%s\n' "$verification_output" \
      | sed -n 's/: FAILED$//p' \
      | while IFS= read -r failed_file; do
          sha256sum "$failed_file"
        done
    exit 1
  fi
  printf '%s\n' "$verification_output"
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
