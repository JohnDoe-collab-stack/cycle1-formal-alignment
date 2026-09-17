#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

manifest_paths="$(mktemp)"
trap 'rm -f "$manifest_paths"' EXIT
awk 'NF >= 2 { print $2 }' MANIFEST.sha256 > "$manifest_paths"

missing_root=0
while IFS= read -r root; do
  relative_path="${root//./\/}.lean"
  if ! grep -Fqx "$relative_path" "$manifest_paths"; then
    if [[ -f "$relative_path" ]]; then
      if command -v sha256sum >/dev/null 2>&1; then
        actual_hash="$(sha256sum "$relative_path" | awk '{print $1}')"
      elif command -v shasum >/dev/null 2>&1; then
        actual_hash="$(shasum --algorithm 256 "$relative_path" | awk '{print $1}')"
      else
        actual_hash="<sha256-unavailable>"
      fi
      echo "Missing manifest entry: ${actual_hash}  ${relative_path}" >&2
    else
      echo "Lake root has no source file: ${relative_path}" >&2
    fi
    missing_root=1
  fi
done < <(sed -n 's/^[[:space:]]*"\([^"]*\)"[,]\{0,1\}[[:space:]]*$/\1/p' lakefile.toml)

if [[ "$missing_root" -ne 0 ]]; then
  exit 1
fi

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
