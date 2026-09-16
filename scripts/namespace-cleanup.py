from __future__ import annotations

from pathlib import Path
import hashlib
import sys

ROOT = Path(__file__).resolve().parents[1]

ALIGNMENT_FILES = [
    "Alignment/Constitutive.lean",
    "Alignment/FinitePersistence.lean",
    "Alignment/ReadoutPersistence.lean",
    "Alignment/MediatedTransitionCoherence.lean",
    "Alignment/MediatedTransitionPasting.lean",
]

CONSUMERS_OPEN_ALIGNMENT = [
    "StrongPerimetralTurning/ConstitutivePersistence.lean",
    "StrongPerimetralTurning/IteratedConstitutivePersistence.lean",
    "StructuralEntrypoint.lean",
    "Examples/ConcreteContinuation/LoggedAlgebra.lean",
    "Examples/Alignment/IteratedReadout.lean",
    "Tests/DynamicAlignmentRegression.lean",
    "Tests/MediatedTransitionCoherenceRegression.lean",
    "Tests/MediatedTransitionPastingRegression.lean",
]

PREFIX_REPLACEMENTS = {
    "StrongPerimetralTurning.ExactTypeTransport": "ExactTypeTransport",
    "StrongPerimetralTurning.MediatedTransitionCoherence": "MediatedTransitionCoherence",
    "StrongPerimetralTurning.ExactOneStepConstitutiveAlignment": "Alignment.ExactOneStepConstitutiveAlignment",
    "StrongPerimetralTurning.DepthExtension": "Alignment.DepthExtension",
    "StrongPerimetralTurning.IteratedCarrier": "Alignment.IteratedCarrier",
    "StrongPerimetralTurning.FiniteConstitutiveAlignment": "Alignment.FiniteConstitutiveAlignment",
    "StrongPerimetralTurning.FiniteFreshValues": "Alignment.FiniteFreshValues",
    "StrongPerimetralTurning.iteratedReadout": "Alignment.iteratedReadout",
    "StrongPerimetralTurning.extendReadout": "Alignment.extendReadout",
    "StrongPerimetralTurning.oneStepAlignment": "Alignment.oneStepAlignment",
}

TEXT_SUFFIXES = {".lean", ".md", ".txt", ".toml", ".cff"}


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def write(path: str, text: str) -> None:
    (ROOT / path).write_text(text, encoding="utf-8")


def replace_last(text: str, old: str, new: str) -> str:
    index = text.rfind(old)
    if index < 0:
        raise RuntimeError(f"missing final marker: {old!r}")
    return text[:index] + new + text[index + len(old):]


def move_outer_namespace(path: str, new_namespace: str | None) -> None:
    text = read(path)
    marker = "namespace StrongPerimetralTurning\n"
    if marker not in text:
        raise RuntimeError(f"{path}: missing outer StrongPerimetralTurning namespace")
    replacement = "" if new_namespace is None else f"namespace {new_namespace}\n"
    text = text.replace(marker, replacement, 1)
    end_marker = "end StrongPerimetralTurning\n"
    end_replacement = "" if new_namespace is None else f"end {new_namespace}\n"
    text = replace_last(text, end_marker, end_replacement)
    write(path, text)


def add_open_alignment(path: str) -> None:
    text = read(path)
    if "open Alignment\n" in text:
        return
    lines = text.splitlines(keepends=True)
    last_import = -1
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import = i
        elif last_import >= 0 and line.strip() != "":
            break
    if last_import < 0:
        raise RuntimeError(f"{path}: no import block found")
    lines.insert(last_import + 1, "\nopen Alignment\n")
    write(path, "".join(lines))


def replace_explicit_prefixes() -> None:
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
            continue
        if ".git" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        updated = text
        for old, new in PREFIX_REPLACEMENTS.items():
            updated = updated.replace(old, new)
        if updated != text:
            path.write_text(updated, encoding="utf-8")


def update_canonical_namespace_docs() -> None:
    fr_path = "docs/fr/cartographie_architecturale_verifiee.md"
    fr = read(fr_path)
    old_fr = """### Namespace et spécialisation\n\nPlusieurs structures génériques (`ExactTypeTransport`, `Alignment/*`,\n`MediatedTransitionCoherence`) vivent actuellement sous le namespace Lean\n`StrongPerimetralTurning`. Cette appartenance nominale **ne suffit pas** à les\nclasser comme spécialisations circulaires. Leur niveau de spécialisation doit\nêtre déterminé par leurs imports et leurs signatures.\n"""
    new_fr = """### Namespace et spécialisation\n\nLes namespaces suivent désormais le niveau de spécialisation réel :\n`ExactTypeTransport` et `MediatedTransitionCoherence` sont des racines génériques,\nles déclarations des modules `Alignment/*` vivent sous `Alignment`, et\n`StrongPerimetralTurning` est réservé à l'instance circulaire et à ses\nspécialisations. Cette séparation nominale reflète le DAG des imports sans\nintroduire de nouvelle dépendance mathématique.\n"""
    if old_fr not in fr:
        raise RuntimeError("French canonical namespace paragraph changed unexpectedly")
    fr = fr.replace(old_fr, new_fr, 1)
    fr = fr.replace(
        "Leur emplacement actuel est donc un fait historique du système de fichiers,\npas une dépendance scientifique à un « instance circulaire ».\n",
        "Leur emplacement sous `Alignment/` correspond désormais à leur propriété\nmathématique générique et non à une spécialisation circulaire.\n",
    )
    write(fr_path, fr)

    en_path = "docs/en/verified_architecture_map.md"
    en = read(en_path)
    old_en = """### Namespace and specialization\n\nSeveral generic structures (`ExactTypeTransport`, `Alignment/*`,\n`MediatedTransitionCoherence`) currently live under the Lean namespace\n`StrongPerimetralTurning`. Namespace membership **is not enough** to classify\nthem as circular specializations. Their specialization level must be determined\nfrom their imports and signatures.\n"""
    new_en = """### Namespace and specialization\n\nNamespaces now follow the actual specialization level: `ExactTypeTransport`\nand `MediatedTransitionCoherence` are generic roots, declarations from\n`Alignment/*` live under `Alignment`, and `StrongPerimetralTurning` is reserved\nfor the circular instance and its specializations. This nominal separation\nmirrors the import DAG without adding any new mathematical dependency.\n"""
    if old_en not in en:
        raise RuntimeError("English canonical namespace paragraph changed unexpectedly")
    en = en.replace(old_en, new_en, 1)
    en = en.replace(
        "Their current location is therefore a historical filesystem fact, not a\nscientific dependency on a “circular instance”.\n",
        "Their location under `Alignment/` now matches their generic mathematical\nrole rather than a circular specialization.\n",
    )
    write(en_path, en)


def update_manifest() -> None:
    manifest = ROOT / "MANIFEST.sha256"
    new_lines: list[str] = []
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        if not raw.strip():
            continue
        _, rel = raw.split("  ", 1)
        payload = (ROOT / rel).read_bytes()
        new_lines.append(f"{hashlib.sha256(payload).hexdigest()}  {rel}")
    manifest.write_text("\n".join(new_lines) + "\n", encoding="utf-8")


def apply() -> None:
    move_outer_namespace("ExactTypeTransport.lean", None)
    move_outer_namespace("MediatedTransitionCoherence.lean", None)
    for path in ALIGNMENT_FILES:
        move_outer_namespace(path, "Alignment")
    for path in CONSUMERS_OPEN_ALIGNMENT:
        add_open_alignment(path)
    replace_explicit_prefixes()
    update_canonical_namespace_docs()
    update_manifest()


def verify() -> None:
    failures: list[str] = []

    for path in ["ExactTypeTransport.lean", "MediatedTransitionCoherence.lean", *ALIGNMENT_FILES]:
        text = read(path)
        if "namespace StrongPerimetralTurning\n" in text or "end StrongPerimetralTurning\n" in text:
            failures.append(f"generic module still nested under StrongPerimetralTurning: {path}")

    for path in ALIGNMENT_FILES:
        text = read(path)
        if "namespace Alignment\n" not in text:
            failures.append(f"alignment module missing namespace Alignment: {path}")

    for path in CONSUMERS_OPEN_ALIGNMENT:
        if "open Alignment\n" not in read(path):
            failures.append(f"alignment consumer missing open Alignment: {path}")

    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in TEXT_SUFFIXES or ".git" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        for stale in PREFIX_REPLACEMENTS:
            if stale in text:
                failures.append(f"stale generic namespace prefix {stale} in {path.relative_to(ROOT)}")

    fr = read("docs/fr/cartographie_architecturale_verifiee.md")
    en = read("docs/en/verified_architecture_map.md")
    if "vivent actuellement sous le namespace Lean\n`StrongPerimetralTurning`" in fr:
        failures.append("French canonical map still reports old namespace layout")
    if "currently live under the Lean namespace\n`StrongPerimetralTurning`" in en:
        failures.append("English canonical map still reports old namespace layout")

    if failures:
        raise SystemExit("\n".join(failures))
    print("namespace cleanup verification: OK")


if __name__ == "__main__":
    if "--verify" in sys.argv:
        verify()
    else:
        apply()
        verify()
