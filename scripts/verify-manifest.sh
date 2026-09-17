#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

echo 'DEPTH_WORDING_AUDIT_BEGIN'
grep -RInE \
  --include='*.md' --include='*.lean' \
  '(finite[- ]depth|finite persistence|finite extension|finite genesis|every finite depth|arbitrary finite depth|later finite depth|profondeur[s]? finie|persistance finie|extension finie|it[eé]ration finie|toute profondeur finie|profondeurs finies)' \
  . || true
echo 'DEPTH_WORDING_AUDIT_END'

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
