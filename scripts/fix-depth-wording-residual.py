from pathlib import Path
import hashlib
import re

replacements = {
    'README_fr.md': [
        ('| persistance finie du résidu opérationnel |', '| persistance du résidu opérationnel pour tout `n : Nat` |'),
        ('La persistance finie est néanmoins quantifiée uniformément sur toute profondeur cible finie arbitraire.', "La persistance est quantifiée uniformément pour toute profondeur cible `n : Nat` arbitraire, sans profondeur maximale fixée."),
        ('dérive la persistance finie, la structure des identités entre profondeurs', 'dérive la persistance uniforme pour tout `n : Nat`, la structure des identités entre profondeurs'),
        ("instancie la persistance finie sur les histoires réellement générées", "instancie la persistance uniforme en `n : Nat` sur les histoires réellement générées"),
        ('exerce la persistance finie et la séparation des identités', 'exerce la persistance à plusieurs profondeurs naturelles et la séparation des identités'),
        ('persistance finie\n        ↓\ntransport cohérent entre réalisations', 'persistance pour tout `n : Nat`\n        ↓\ntransport cohérent entre réalisations'),
        ("l'alignement constitutif fini", "l'alignement constitutif indexé par une profondeur naturelle"),
    ],
    'docs/fr/cartographie_architecturale_verifiee.md': [
        ('`Alignment.FinitePersistence` ajoute la profondeur finie, les extensions et les\ntransports par indice constitutif.', '`Alignment.FinitePersistence` ajoute une profondeur `n : Nat` arbitraire, les extensions et les\ntransports par indice constitutif.'),
        ("L'application actuelle à l'alignement fini est :", "L'application actuelle à l'alignement indexé par une profondeur naturelle arbitraire est :"),
        ("## 4. Persistance finie de l'instance circulaire", "## 4. Persistance uniforme en profondeur naturelle de l'instance circulaire"),
        ("Il construit réellement les histoires finies de l'instance :", "Il construit réellement les histoires `iteratedHistory n` pour un `n : Nat` arbitraire :"),
        ("La lecture est « persistance finie de l'instance circulaire », et non", "La lecture est « persistance uniforme pour tout `n : Nat` de l'instance circulaire », et non"),
    ],
    'docs/en/verified_architecture_map.md': [
        ('`Alignment.FinitePersistence` adds finite depth, extensions, and transports\nthrough a constitutive index.', '`Alignment.FinitePersistence` adds an arbitrary `n : Nat` depth, extensions, and transports\nthrough a constitutive index.'),
        ('Its current application to finite alignment is:', 'Its current application to alignment at arbitrary natural-number depth is:'),
        ('## 4. Finite persistence of the circular instance', '## 4. Persistence of the circular instance uniform in natural-number depth'),
        ('It actually constructs the finite histories of the instance:', 'It actually constructs `iteratedHistory n` for an arbitrary `n : Nat`:'),
        ('The correct reading is “finite persistence of the circular instance”, not “a\nsecond constitution of circularity”.', 'The correct reading is “persistence of the circular instance uniform for every `n : Nat`”, not “a\nsecond constitution of circularity”.'),
    ],
    'StructuralEntrypoint.lean': [
        ('finite extension is independent of its proof-relevant depth witness', 'natural-depth extension is independent of its proof-relevant depth witness'),
        ('readout assembled afterward by finite extension', 'readout assembled afterward by extension to an arbitrary natural-number depth'),
        ('Finite extension and change of realization commute', 'Natural-depth extension and change of realization commute'),
        ('Finite extension on actual circular realizations depends only on its source and', 'Natural-depth extension on actual circular realizations depends only on its source and'),
        ('Finite extension remains witness-independent', 'Natural-depth extension remains witness-independent'),
        ('The finite depth `0 → 1` extension', 'The depth `0 → 1` extension'),
    ],
    'StrongPerimetralTurning/IteratedConstitutivePersistence.lean': [
        ('Finite extension between two supplied concrete realizations depends only on', 'Natural-depth extension between two supplied concrete realizations depends only on'),
    ],
    'Alignment/ReadoutPersistence.lean': [
        ('readout constructed by finite extension retains its earlier values', 'readout constructed by extension to an arbitrary natural-number depth retains its earlier values'),
        ('one value per finite extension', 'one value per natural-depth extension'),
        ('persists through finite extension', 'persists through extension to an arbitrary natural-number depth'),
    ],
    'Alignment/FinitePersistence.lean': [
        ('# Finite constitutive persistence', '# Constitutive persistence at arbitrary natural depth'),
        ('This module derives finite-depth alignment from a common constitutive index.', 'This module derives alignment at an arbitrary natural-number depth from a common constitutive index.'),
        ('A positively constructed finite extension from one depth to another.', 'A positively constructed extension between two natural-number depths.'),
        ('Construct the finite extension from depth zero to any supplied depth.', 'Construct the extension from depth zero to any supplied natural-number depth.'),
        ('Compose two finite depth extensions.', 'Compose two extensions between natural-number depths.'),
        ('The finite constitutive carrier at depth `n`', 'The constitutive carrier at arbitrary depth `n : Nat`'),
        ('Preserve every existing identity in the next finite carrier.', 'Preserve every existing identity in the next natural-depth carrier.'),
        ('Embed an initial identity into any finite constitutive depth.', 'Embed an initial identity into any natural-number constitutive depth.'),
        ('A depth-independent structural code for finite identities.', 'A depth-independent structural code for identities at arbitrary natural depth.'),
        ('Every finite extension preserves the same structural identity code.', 'Every extension between natural-number depths preserves the same structural identity code.'),
        ('One carrier at a finite constitutive depth, exactly indexed by the canonical\nfinite carrier.', 'One carrier at an arbitrary natural-number constitutive depth, exactly indexed by the canonical\ncarrier at that depth.'),
        ('One exact concrete realization of a finite-depth constitutive carrier.', 'One exact concrete realization of a constitutive carrier at an arbitrary natural-number depth.'),
        ('The derived spoke from the common finite index', 'The derived spoke from the common natural-depth index'),
        ('Concrete finite extension is independent of its depth witness.', 'Concrete natural-depth extension is independent of its depth witness.'),
        ('Finite extension commutes with change of exact realization.', 'Natural-depth extension commutes with change of exact realization.'),
    ],
    'Alignment/ConstitutiveProfileReconstruction.lean': [
        ('finite transport is the canonical lift', 'transport at that depth is the canonical lift'),
    ],
    'Alignment/FiniteAnchoredMatchSearch.lean': [
        ('`TotalAnchoredMatching`, exact transport, and finite genesis transport without', '`TotalAnchoredMatching`, exact transport, and genesis transport at any requested natural-number depth without'),
        ('Search for the corresponding exact transport at any finite genesis depth.', 'Search for the corresponding exact transport at any requested natural-number genesis depth.'),
    ],
    'Alignment/DirectionalGenesisPersistence.lean': [
        ('Construct the finite genesis embedding induced by an injective initial map.', 'Construct the genesis embedding at an arbitrary natural depth induced by an injective initial map.'),
    ],
    'Tests/GenesisReconstructionRegression.lean': [
        ('# Regression checks for finite genesis reconstruction', '# Regression checks for genesis reconstruction at arbitrary natural depth'),
        ('requires the whole finite genesis stratification', 'requires the whole natural-depth genesis stratification'),
    ],
    'Tests/DirectionalGenesisPersistenceRegression.lean': [
        ('persists injectively through finite genesis', 'persists injectively through arbitrary natural-depth genesis'),
        ('no forward finite genesis embedding', 'no forward genesis embedding at a natural depth'),
        ('no backward finite genesis embedding', 'no backward genesis embedding at a natural depth'),
    ],
    'Tests/FiniteAnchoredMatchSearchRegression.lean': [
        ('propagates through finite genesis depth', 'propagates through arbitrary natural-number genesis depth'),
        ('exposes the finite genesis transport directly', 'exposes the transport at the requested natural-number genesis depth directly'),
    ],
    'Tests/GenesisRigidityRegression.lean': [
        ('persists at every chosen finite genesis depth', 'persists at every chosen natural-number genesis depth'),
    ],
    'Tests/ConstitutiveProfileReconstructionRegression.lean': [
        ('extends canonically through finite genesis', 'extends canonically through arbitrary natural-depth genesis'),
    ],
    'Tests/AnchoredMatchReconstructionRegression.lean': [
        ('propagates through finite genesis', 'propagates through arbitrary natural-depth genesis'),
    ],
    'Examples/Alignment/IteratedReadout.lean': [
        ('instantiates the finite persistence laws at three generated', 'instantiates the persistence laws at three generated'),
    ],
}

changed = []
missing = []
for filename, pairs in replacements.items():
    path = Path(filename)
    text = path.read_text(encoding='utf-8')
    original = text
    for old, new in pairs:
        if old not in text:
            missing.append((filename, old))
            continue
        text = text.replace(old, new)
    if text != original:
        path.write_text(text, encoding='utf-8')
        changed.append(filename)

manifest = Path('MANIFEST.sha256')
lines = []
for raw in manifest.read_text(encoding='utf-8').splitlines():
    if not raw.strip():
        continue
    _old_hash, filename = raw.split('  ', 1)
    data = Path(filename).read_bytes()
    lines.append(f'{hashlib.sha256(data).hexdigest()}  {filename}')
manifest.write_text('\n'.join(lines) + '\n', encoding='utf-8')

print('RESIDUAL_CORRECTED_FILES_BEGIN')
for name in changed:
    print(name)
print('RESIDUAL_CORRECTED_FILES_END')
print('RESIDUAL_MISSING_EXPECTED_BEGIN')
for filename, old in missing:
    print(f'{filename}: {old!r}')
print('RESIDUAL_MISSING_EXPECTED_END')

pattern = re.compile(r'(finite[- ]depth|finite persistence|finite extension|finite genesis|every finite depth|arbitrary finite depth|later finite depth|profondeur[s]? finie|persistance finie|extension finie|it[eé]ration finie|toute profondeur finie|profondeurs finies)', re.I)
print('FINAL_RESIDUAL_DEPTH_WORDING_BEGIN')
for path in list(Path('.').rglob('*.md')) + list(Path('.').rglob('*.lean')):
    if '.lake' in path.parts:
        continue
    for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if pattern.search(line):
            print(f'{path}:{number}:{line}')
print('FINAL_RESIDUAL_DEPTH_WORDING_END')
