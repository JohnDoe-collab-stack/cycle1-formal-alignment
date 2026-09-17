#!/usr/bin/env bash

set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

echo 'ALIGNMENT_MANIFEST_HASHES_BEGIN'
sha256sum \
  Alignment/AnchoredMatchReconstruction.lean \
  Alignment/AnchoredMatchStrictness.lean \
  Alignment/AnchoredRelationReconstruction.lean \
  Alignment/ConstitutiveProfileReconstruction.lean \
  Alignment/ConstitutiveProfileRigidity.lean \
  Alignment/DirectionalGenesisPersistence.lean \
  Alignment/FiniteAlignmentClassification.lean \
  Alignment/FiniteAnchoredMatchDecision.lean \
  Alignment/FiniteAnchoredMatchSearch.lean \
  Alignment/GenesisCharacterization.lean \
  Alignment/GenesisReconstruction.lean \
  Alignment/GenesisRigidity.lean \
  Tests/AnchoredMatchReconstructionRegression.lean \
  Tests/AnchoredMatchStrictnessRegression.lean \
  Tests/AnchoredRelationReconstructionRegression.lean \
  Tests/ConstitutiveProfileReconstructionRegression.lean \
  Tests/ConstitutiveProfileRigidityRegression.lean \
  Tests/DirectionalGenesisPersistenceRegression.lean \
  Tests/FiniteAlignmentClassificationRegression.lean \
  Tests/FiniteAnchoredMatchSearchRegression.lean \
  Tests/GenesisReconstructionRegression.lean \
  Tests/GenesisRigidityRegression.lean
echo 'ALIGNMENT_MANIFEST_HASHES_END'

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check --strict MANIFEST.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum --algorithm 256 --check MANIFEST.sha256
else
  echo 'No SHA-256 verification command found (sha256sum or shasum).' >&2
  exit 1
fi
