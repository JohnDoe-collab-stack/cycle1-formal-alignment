#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = Path('.github/workflows/cycle1-refactor-audit.yml')
SCRIPT = Path('scripts/refactor-cycle1.py')


def tracked_text_paths():
    raw = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).split(b'\0')
    for item in raw:
        if not item:
            continue
        rel = Path(item.decode())
        path = ROOT / rel
        if rel in {WORKFLOW, SCRIPT} or not path.is_file():
            continue
        try:
            path.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            continue
        yield rel, path


def replace_all(replacements, predicate=lambda _rel: True):
    for rel, path in tracked_text_paths():
        if not predicate(rel):
            continue
        text = path.read_text(encoding='utf-8')
        original = text
        for old, new in replacements:
            text = text.replace(old, new)
        if text != original:
            path.write_text(text, encoding='utf-8')


def relocate():
    moves = {
        'Cycle1/ConstitutivePersistence.lean':
            'StrongPerimetralTurning/ConstitutivePersistence.lean',
        'Cycle1/IteratedConstitutivePersistence.lean':
            'StrongPerimetralTurning/IteratedConstitutivePersistence.lean',
        'Cycle1/MediatedTransitionCoherence.lean':
            'Alignment/MediatedTransitionCoherence.lean',
        'Cycle1/MediatedTransitionPasting.lean':
            'Alignment/MediatedTransitionPasting.lean',
    }
    for source, target in moves.items():
        (ROOT / target).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'mv', source, target], cwd=ROOT, check=True)

    replace_all([
        ('Cycle1.IteratedConstitutivePersistence',
         'StrongPerimetralTurning.IteratedConstitutivePersistence'),
        ('Cycle1.ConstitutivePersistence',
         'StrongPerimetralTurning.ConstitutivePersistence'),
        ('Cycle1.MediatedTransitionCoherence',
         'Alignment.MediatedTransitionCoherence'),
        ('Cycle1.MediatedTransitionPasting',
         'Alignment.MediatedTransitionPasting'),
        ('Cycle1/IteratedConstitutivePersistence.lean',
         'StrongPerimetralTurning/IteratedConstitutivePersistence.lean'),
        ('Cycle1/ConstitutivePersistence.lean',
         'StrongPerimetralTurning/ConstitutivePersistence.lean'),
        ('Cycle1/MediatedTransitionCoherence.lean',
         'Alignment/MediatedTransitionCoherence.lean'),
        ('Cycle1/MediatedTransitionPasting.lean',
         'Alignment/MediatedTransitionPasting.lean'),
    ])


def rename_api():
    replacements = [
        ('cycle1ResidualOccurrence_extension_transport_natural',
         'iteratedResidualOccurrence_extension_transport_natural'),
        ('cycle1Transport_one_backward_eq_oneStep',
         'iteratedTransport_one_backward_eq_oneStep'),
        ('cycle1Realization_previous_isEarlier',
         'iteratedRealization_previous_isEarlier'),
        ('cycle1Realization_one_fresh_eq_residual',
         'iteratedRealization_one_fresh_eq_residual'),
        ('cycle1ResidualOccurrence_transport_natural',
         'iteratedResidualOccurrence_transport_natural'),
        ('cycle1Extension_witness_independent',
         'iteratedExtension_witness_independent'),
        ('cycle1Realization_one_fresh_eq_oneStep',
         'iteratedRealization_one_fresh_eq_oneStep'),
        ('cycle1ResidualOccurrence_persists',
         'iteratedResidualOccurrence_persists'),
        ('cycle1Extension_zero_one_eq_oneStep',
         'iteratedExtension_zero_one_eq_oneStep'),
        ('cycle1Realization_fresh_isLast',
         'iteratedRealization_fresh_isLast'),
        ('cycle1_extend_transport_natural',
         'iterated_extend_transport_natural'),
        ('cycle1Transport_one_eq_oneStep',
         'iteratedTransport_one_eq_oneStep'),
        ('cycle1Realization_atIndex',
         'iteratedRealization_atIndex'),
        ('cycle1Alignment_one_backward',
         'iteratedAlignment_one_backward'),
        ('cycle1Alignment_one_forward',
         'iteratedAlignment_one_forward'),
        ('cycle1Realization', 'iteratedRealization'),
        ('cycle1Alignment', 'iteratedAlignment'),
    ]
    replace_all(replacements)


def english_pairs():
    return [
        ('# Cycle 1 — Relative alignment to an independent specification',
         '# Relative alignment of the circular instance to an independent specification'),
        ('# Cycle 1 — Relative alignment', '# Circular instance — relative alignment'),
        ('Cycle 1 — relative alignment', 'Circular instance — relative alignment'),
        ('In this Cycle 1 instance', 'In the circular instance'),
        ('in this Cycle 1 instance', 'in the circular instance'),
        ('the actual Cycle 1 producer', 'the actual circular producer'),
        ('actual Cycle 1 producer', 'actual circular producer'),
        ('actual Cycle 1 histories', 'actual circular histories'),
        ('real Cycle 1 histories', 'real circular histories'),
        ('actual Cycle 1 generations', 'actual circular generations'),
        ('actual Cycle 1 carrier', 'actual circular carrier'),
        ('actual Cycle 1 realizations', 'actual circular realizations'),
        ('actual Cycle 1 occurrences', 'actual circular occurrences'),
        ('Cycle 1 residual-determination core', 'circular residual-determination core'),
        ('Cycle 1 core', 'circular core'),
        ('Cycle 1 alignment', 'circular alignment'),
        ('Cycle 1 continuation', 'circular continuation'),
        ('Cycle 1 proposition-level adequacy',
         'circular regime/specification proposition-level adequacy'),
        ('proposition-level Cycle 1 adequacy',
         'proposition-level circular regime/specification adequacy'),
        ('Cycle 1 adequacy', 'circular regime/specification adequacy'),
        ('The two Cycle 1 maps', 'The two circular regime/specification witness maps'),
        ('two Cycle 1 maps', 'two circular regime/specification witness maps'),
        ('Cycle 1 maps', 'circular regime/specification witness maps'),
        ('Cycle 1 witness families', 'circular regime/specification witness families'),
        ('Cycle 1 families', 'circular regime/specification families'),
        ('Cycle 1 norm', 'circular specification'),
        ('Cycle 1 declarations', 'circular-instance declarations'),
        ('Cycle 1 modules', 'circular-instance modules'),
        ('Cycle 1 proof', 'circular-instance proof'),
        ('Cycle 1 result', 'circular-instance result'),
        ('Cycle 1 library', 'circular foundations library'),
        ('Cycle 1 content', 'circular-instance content'),
        ('every later finite Cycle 1 depth', 'every later finite circular depth'),
        ('every later Cycle 1 stage', 'every later circular stage'),
        ('finite Cycle 1 realization', 'finite circular realization'),
        ('finite Cycle 1 depth', 'finite circular depth'),
        ('finite Cycle 1 histories', 'finite circular histories'),
        ('Cycle 1 steps', 'circular generation steps'),
        ('of Cycle 1', 'of the circular instance'),
        ('from Cycle 1', 'from the circular instance'),
        ('to Cycle 1', 'to the circular instance'),
        ('in Cycle 1', 'in the circular instance'),
        ('within Cycle 1', 'within the circular instance'),
        ('for Cycle 1', 'for the circular instance'),
        ('by Cycle 1', 'by the circular instance'),
        ('Cycle 1 is', 'The circular instance is'),
        ('Cycle 1 does', 'The circular instance does'),
        ('Cycle 1 provides', 'The circular instance provides'),
        ('Cycle 1 constructs', 'The circular instance constructs'),
        ('Cycle 1 verifies', 'The circular instance verifies'),
        ('Cycle 1 establishes', 'The circular instance establishes'),
        ('Cycle 1 machine-checks', 'The circular instance machine-checks'),
        ('Cycle 1 separates', 'The circular instance separates'),
        ('cycle 1 modules', 'circular-instance modules'),
        ('from cycle 1', 'from the circular instance'),
        ('of cycle 1', 'of the circular instance'),
        ('in cycle 1', 'in the circular instance'),
        ('the cycle 1 application', 'the circular application'),
        ('cycle 1 application', 'circular application'),
        ('cycle 1', 'circular instance'),
        ('Cycle 1', 'circular instance'),
    ]


def french_pairs():
    return [
        ('# Cycle 1 — Alignement relatif à une spécification indépendante',
         "# Alignement relatif de l'instance circulaire à une spécification indépendante"),
        ('# Cycle 1 — Alignement relatif', '# Instance circulaire — alignement relatif'),
        ('Cycle 1 — alignement relatif', 'Instance circulaire — alignement relatif'),
        ('Dans cette instance du Cycle 1', "Dans l'instance circulaire"),
        ('dans cette instance du Cycle 1', "dans l'instance circulaire"),
        ('producteur réel du Cycle 1', 'producteur circulaire réel'),
        ('histoires réelles du Cycle 1', 'histoires circulaires réelles'),
        ('générations réelles du Cycle 1', 'générations circulaires réelles'),
        ('instance du Cycle 1', 'instance circulaire'),
        ('adéquation propositionnelle du Cycle 1',
         "adéquation propositionnelle régime/spécification de l'instance circulaire"),
        ('adéquation du Cycle 1',
         "adéquation régime/spécification de l'instance circulaire"),
        ('adéquation Cycle 1',
         "adéquation régime/spécification de l'instance circulaire"),
        ('Les deux applications du Cycle 1',
         "Les deux applications de témoins de l'instance circulaire"),
        ('deux applications du Cycle 1',
         "deux applications de témoins de l'instance circulaire"),
        ('familles originelles du Cycle 1',
         "familles originelles de l'instance circulaire"),
        ('familles de témoins du Cycle 1',
         "familles de témoins de l'instance circulaire"),
        ('norme du cycle 1', 'spécification circulaire'),
        ('modules du cycle 1', "modules de l'instance circulaire"),
        ('preuve du Cycle 1', "preuve de l'instance circulaire"),
        ('résultat central du Cycle 1', "résultat central de l'instance circulaire"),
        ('contenu du Cycle 1', "contenu de l'instance circulaire"),
        ('profondeur finie du Cycle 1', 'profondeur circulaire finie'),
        ('étape du Cycle 1', 'étape de génération circulaire'),
        ('étapes du Cycle 1', 'étapes de génération circulaire'),
        ('du Cycle 1', "de l'instance circulaire"),
        ('au Cycle 1', "à l'instance circulaire"),
        ('dans le Cycle 1', "dans l'instance circulaire"),
        ('pour le Cycle 1', "pour l'instance circulaire"),
        ('par le Cycle 1', "par l'instance circulaire"),
        ('Le Cycle 1 est', "L'instance circulaire est"),
        ('Le Cycle 1 fournit', "L'instance circulaire fournit"),
        ('Le Cycle 1 vérifie', "L'instance circulaire vérifie"),
        ('Le Cycle 1 sépare', "L'instance circulaire sépare"),
        ('Le Cycle 1', "L'instance circulaire"),
        ('le Cycle 1', "l'instance circulaire"),
        ('du cycle 1', "de l'instance circulaire"),
        ('au cycle 1', "à l'instance circulaire"),
        ('dans le cycle 1', "dans l'instance circulaire"),
        ('Le cycle 1', "L'instance circulaire"),
        ('le cycle 1', "l'instance circulaire"),
        ('cycle 1', 'instance circulaire'),
        ('Cycle 1', 'instance circulaire'),
    ]


def documentation():
    replace_all([('Cycle1Alignment', 'StructuralFoundations')])

    for rel, path in tracked_text_paths():
        is_french = rel == Path('README_fr.md') or str(rel).startswith('docs/fr/')
        is_english = (
            rel == Path('README.md')
            or str(rel).startswith('docs/en/')
            or rel.suffix == '.lean'
            or rel == Path('audit/AUDIT_BUILD.txt')
        )
        if not (is_french or is_english):
            continue
        text = path.read_text(encoding='utf-8')
        original = text
        for old, new in (french_pairs() if is_french else english_pairs()):
            text = text.replace(old, new)
        if text != original:
            path.write_text(text, encoding='utf-8')

    fr_map = ROOT / 'docs/fr/cartographie_architecturale_verifiee.md'
    fr_text = fr_map.read_text(encoding='utf-8')
    fr_section = '''## 9. Classement après le refactor architectural

Le classement numérique historique a été dissous sans modifier le contenu
mathématique des théorèmes. Les modules sont désormais rangés selon leur
propriétaire scientifique :

- `StrongPerimetralTurning/ConstitutivePersistence.lean` et
  `StrongPerimetralTurning/IteratedConstitutivePersistence.lean` développent
  l'instance circulaire ;
- `Alignment/MediatedTransitionCoherence.lean` et
  `Alignment/MediatedTransitionPasting.lean` spécialisent le noyau générique de
  cohérence médiée à `FiniteConstitutiveAlignment`.

Les identifiants d'itération utilisent désormais le préfixe `iterated` plutôt
qu'un numéro de phase. Le target Lean principal porte le même nom architectural
que le package, `StructuralFoundations`, tandis que `RepresentationBoundary`
reste un target séparé. Cette organisation matérialise le DAG vérifié dans les
chemins du dépôt sans introduire de nouvelle hiérarchie scientifique.
'''
    fr_text = re.sub(r'## 9\..*\Z', fr_section, fr_text, flags=re.S)
    fr_map.write_text(fr_text, encoding='utf-8')

    en_map = ROOT / 'docs/en/verified_architecture_map.md'
    en_text = en_map.read_text(encoding='utf-8')
    en_section = '''## 9. Classification after the architectural refactor

The historical numbered classification has been dissolved without changing the
mathematical content of the theorems. Modules are now placed under their actual
scientific owner:

- `StrongPerimetralTurning/ConstitutivePersistence.lean` and
  `StrongPerimetralTurning/IteratedConstitutivePersistence.lean` develop the
  circular instance;
- `Alignment/MediatedTransitionCoherence.lean` and
  `Alignment/MediatedTransitionPasting.lean` specialize the generic mediated
  coherence kernel to `FiniteConstitutiveAlignment`.

Iteration declarations now use the `iterated` prefix rather than a phase
number. The primary Lean target uses the package's architectural name,
`StructuralFoundations`, while `RepresentationBoundary` remains a separate
target. This organization makes the verified DAG visible in repository paths
without introducing a new scientific hierarchy.
'''
    en_text = re.sub(r'## 9\..*\Z', en_section, en_text, flags=re.S)
    en_map.write_text(en_text, encoding='utf-8')


def refresh_manifest():
    manifest = ROOT / 'MANIFEST.sha256'
    paths = []
    for line in manifest.read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        _, name = line.split('  ', 1)
        paths.append(name)
    lines = []
    for name in paths:
        path = ROOT / name
        if not path.is_file():
            raise SystemExit(f'manifest path missing after refactor: {name}')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f'{digest}  {name}')
    manifest.write_text('\n'.join(lines) + '\n', encoding='utf-8')


def verify_legacy_absent():
    if (ROOT / 'Cycle1').exists():
        raise SystemExit('historical numbered directory still exists')
    patterns = [
        re.compile(r'Cycle1'),
        re.compile(r'Cycle 1'),
        re.compile(r'cycle 1'),
        re.compile(r'\bcycle1[A-Za-z0-9_]+\b'),
    ]
    failures = []
    for rel, path in tracked_text_paths():
        text = path.read_text(encoding='utf-8')
        for number, line in enumerate(text.splitlines(), 1):
            if any(p.search(line) for p in patterns):
                failures.append(f'{rel}:{number}:{line}')
    if failures:
        print('Legacy architectural terminology remains:', file=sys.stderr)
        print('\n'.join(failures), file=sys.stderr)
        raise SystemExit(1)


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: refactor-cycle1.py relocate|rename-api|documentation|manifest|verify')
    phase = sys.argv[1]
    actions = {
        'relocate': relocate,
        'rename-api': rename_api,
        'documentation': documentation,
        'manifest': refresh_manifest,
        'verify': verify_legacy_absent,
    }
    try:
        action = actions[phase]
    except KeyError:
        raise SystemExit(f'unknown phase: {phase}')
    action()


if __name__ == '__main__':
    main()
