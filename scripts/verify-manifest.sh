#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

hash_file() {
  local relative_path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$relative_path" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum --algorithm 256 "$relative_path" | awk '{print $1}'
  else
    echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
    exit 1
  fi
}

manifest_paths="$(mktemp)"
trap 'rm -f "$manifest_paths"' EXIT
awk 'NF >= 2 { print $2 }' MANIFEST.sha256 > "$manifest_paths"

failure=0
while IFS= read -r root; do
  relative_path="${root//./\/}.lean"
  if ! grep -Fqx "$relative_path" "$manifest_paths"; then
    if [[ -f "$relative_path" ]]; then
      actual_hash="$(hash_file "$relative_path")"
      echo "Missing manifest entry: ${actual_hash}  ${relative_path}" >&2
    else
      echo "Lake root has no source file: ${relative_path}" >&2
    fi
    failure=1
  fi
done < <(sed -n 's/^[[:space:]]*"\([^"]*\)"[,]\{0,1\}[[:space:]]*$/\1/p' lakefile.toml)

while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  if [[ ! "$line" =~ ^([0-9a-f]{64})\ \ (.+)$ ]]; then
    echo "Malformed manifest line: ${line}" >&2
    failure=1
    continue
  fi

  expected_hash="${BASH_REMATCH[1]}"
  relative_path="${BASH_REMATCH[2]}"
  if [[ ! -f "$relative_path" ]]; then
    echo "Missing file: ${relative_path}" >&2
    failure=1
    continue
  fi

  actual_hash="$(hash_file "$relative_path")"
  if [[ "$actual_hash" != "$expected_hash" ]]; then
    echo "Hash mismatch: ${relative_path}" >&2
    echo "  expected: ${expected_hash}" >&2
    echo "  actual:   ${actual_hash}" >&2
    failure=1
  else
    echo "${relative_path}: OK"
  fi
done < MANIFEST.sha256

if [[ "$failure" -ne 0 ]]; then
  exit 1
fi

echo 'Manifest verification succeeded.'
