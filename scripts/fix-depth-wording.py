from pathlib import Path
import hashlib
import re

replacements = {
    'PRESENTATION_LONGUE.md': [
        ('### 6.4 Provenance structurelle des identités finies', '### 6.4 Provenance structurelle à profondeur naturelle arbitraire'),
        ('L’itération finie ne se contente pas de conserver des éléments dans des carriers successifs.', "L'itération indexée par un naturel arbitraire ne se contente pas de conserver des éléments dans des carriers successifs."),
        ('identité à une profondeur finie', 'identité à une profondeur `n : Nat`'),
        ('La profondeur joue ici le rôle d’un index de genèse dans la construction finie.', "La profondeur joue ici le rôle d'un index de genèse dans une construction indexée par un naturel arbitraire."),
        ('Une extension finie `DepthExtension source target` est proof-relevant', 'Une extension `DepthExtension source target` entre profondeurs naturelles est proof-relevant'),
        ('une même extension finie', 'une même extension entre profondeurs naturelles'),
        ('Cette identité est ensuite prolongée à toute profondeur finie ultérieure fournie.', 'Cette identité est ensuite prolongée à toute profondeur naturelle ultérieure arbitrairement choisie.'),
        ('extension finie\n        ↓\nmême identité à une profondeur ultérieure', 'extension vers une profondeur naturelle arbitraire\n        ↓\nmême identité à une profondeur ultérieure'),
        ('À profondeur finie, l’index est `IteratedCarrier` et conserve les identités initiales ainsi que la profondeur de genèse de chaque identité fraîche.', 'Pour tout `n : Nat`, l’index `IteratedCarrier Initial n` conserve les identités initiales ainsi que la profondeur de genèse de chaque identité fraîche.'),
        ('À profondeur finie, on peut construire une permutation exacte et bijective qui échange deux identités fraîches tout en conservant des aller-retour parfaits.', 'À la profondeur 3, le développement construit une permutation exacte et bijective qui échange deux identités fraîches tout en conservant des aller-retour parfaits.'),
        ('Dans l’alignement constitutif fini, le médiateur est précisément `IteratedCarrier`.', "Dans l'alignement constitutif indexé par une profondeur naturelle arbitraire, le médiateur est précisément `IteratedCarrier`."),
        ('Cette propriété est ensuite stable sous extension finie :', 'Cette propriété est ensuite stable sous extension vers toute profondeur naturelle ultérieure :'),
        ('Elle est actuellement uniforme sur toute profondeur **finie** fournie. Elle ne construit pas un carrier concret à l’étape `ω`.', "Elle est uniforme pour tout `n : Nat`. Il n'existe donc aucune profondeur maximale fixée par ces théorèmes. Elle ne construit pas pour autant un carrier concret à l'étape `ω`."),
        ('persistance finie\n        ↓\ntransports induits entre réalisations', 'persistance pour tout `n : Nat`\n        ↓\ntransports induits entre réalisations'),
    ],
    'POSITIONNEMENT_SCIENTIFIQUE.md': [
        ('pour la persistance finie et la naturalité des transports', 'pour la persistance uniforme pour tout `n : Nat` et la naturalité des transports'),
        ('la persistance à profondeur finie et la naturalité entre extension et changement de réalisation', 'la persistance uniforme pour tout `n : Nat` et la naturalité entre extension et changement de réalisation'),
        ('- La persistance démontrée est actuellement finie.', "- La persistance démontrée est uniforme pour tout `n : Nat` et n'impose aucune profondeur maximale. Le dépôt ne construit pas pour autant un carrier concret à l'étape `ω`."),
    ],
    'SCIENTIFIC_POSITIONING.md': [
        ('for finite persistence and naturality of transports', 'for persistence uniform over every `n : Nat` and transport naturality'),
        ('finite-depth persistence, and naturality between extension and change of realization', 'persistence uniform for every `n : Nat`, and naturality between extension and change of realization'),
        ('- The persistence currently proved is finite.', '- The proved persistence is uniform for every `n : Nat` and imposes no maximum depth. The repository does not, however, construct a concrete carrier at an `ω` stage.'),
    ],
    'README_fr.md': [
        ('à travers toute extension finie fournie', 'à travers toute extension vers une profondeur naturelle arbitraire'),
        ('persistance finie\n    ↓\ntransport entre réalisations', 'persistance pour tout `n : Nat`\n    ↓\ntransport entre réalisations'),
        ('pont entre détermination résiduelle et persistance finie', 'pont entre détermination résiduelle et persistance uniforme pour tout `n : Nat`'),
        ('À profondeur finie, le même mécanisme est itéré sur les histoires réellement produites par `generate` et `appendGenerated`.', 'Pour tout `n : Nat`, le même mécanisme est itéré sur les histoires réellement produites par `generate` et `appendGenerated`.'),
        ('## 11. Persistance finie et naturalité', '## 11. Persistance uniforme pour toute profondeur naturelle et naturalité'),
        ('Pour les profondeurs finies, le projet démontre :', 'Pour tout `n : Nat`, le projet démontre :'),
        ("Le dépôt ne possède ni objet d'histoire infinie ni carrier concret à l'étape ω. La persistance est néanmoins uniforme pour toute profondeur finie arbitraire, plutôt qu'énoncée par un théorème distinct pour chaque profondeur.", "Le dépôt ne possède ni objet d'histoire infinie ni carrier concret à l'étape ω. Cela ne borne pas la profondeur : les théorèmes de persistance sont uniformes pour un `n : Nat` arbitraire et n'imposent aucune profondeur maximale."),
        ('machinerie générale de persistance finie', 'machinerie générale de persistance uniforme pour tout `n : Nat`'),
        ('persistance finie\n        ↓\ntransport exact entre réalisations', 'persistance pour tout `n : Nat`\n        ↓\ntransport exact entre réalisations'),
    ],
    'README.md': [
        ('structural reconstruction, finite persistence, and coherent transport', 'structural reconstruction, persistence at arbitrary natural-number depth, and coherent transport'),
        ('tracked through later finite extensions', 'tracked through extensions to arbitrary later natural-number depths'),
        ('→ finite persistence\n→ alignment', '→ persistence for every `n : Nat`\n→ alignment'),
        ('finite extension\n        ↓\ntransport between exact realizations', 'extension to an arbitrary natural-number depth\n        ↓\ntransport between exact realizations'),
        ('finite indexing, extension, transport, composition and naturality', 'natural-depth indexing, extension, transport, composition and naturality'),
        ('circular finite-depth persistence instance', 'circular persistence instance at arbitrary natural-number depth'),
        ('persists through arbitrary later finite depths', 'persists through arbitrary later natural-number depths'),
        ('The persistence results are uniform over arbitrary **finite** depth. The repository does not construct an infinite history object or an ω-stage concrete carrier.', 'The persistence results are uniform for every `n : Nat` and impose no fixed maximum depth. The repository does not construct an infinite history object or an `ω`-stage concrete carrier.'),
    ],
    'docs/fr/alignement_relatif.md': [
        ('### 6.2 Persistance constitutive finie', '### 6.2 Persistance constitutive à profondeur naturelle arbitraire'),
        ("La décomposition à un pas est itérée sans chaîne ω. `DepthExtension k n` est\nun témoin fini positif que la profondeur `n` a été atteinte depuis `k`, et\n`IteratedCarrier I n` conserve le porteur initial tout en ajoutant une identité\nnouvelle à chaque étape.", "La décomposition à un pas est itérée sans chaîne ω. Les profondeurs `k` et `n`\nsont arbitraires dans `Nat`. `DepthExtension k n` est un témoin positif que la\nprofondeur `n` a été atteinte depuis `k`, et `IteratedCarrier I n` conserve le\nporteur initial tout en ajoutant une identité nouvelle à chaque étape. Ces lois\nsont uniformes en `n : Nat` et n'imposent aucune profondeur maximale."),
        ('les deux directions du raccord fini et les deux directions\ndu transport horizontal fini', 'les deux directions du raccord à cette profondeur et les deux directions\ndu transport horizontal à cette profondeur'),
        ("L'identité nouvelle finie réalisée est l'identité `fresh`", "L'identité fraîche réalisée à la profondeur un est l'identité `fresh`"),
        ('depuis sa propre profondeur finie de constitution', "depuis sa propre profondeur naturelle de constitution, quelle qu'elle soit"),
        ('Sous le prolongement fini de la lecture,\ntoute distinction déjà établie à la profondeur `k` persiste à chaque profondeur\nultérieure fournie.', 'Sous le prolongement de la lecture vers une profondeur naturelle ultérieure arbitraire,\ntoute distinction déjà établie à la profondeur `k` persiste à cette profondeur.'),
    ],
    'docs/en/relative_alignment.md': [
        ('### 6.2 Finite constitutive persistence', '### 6.2 Constitutive persistence at arbitrary natural depth'),
        ('The one-step split is iterated without an ω-chain. `DepthExtension k n` is a\npositive finite witness that depth `n` was reached from depth `k`, and\n`IteratedCarrier I n` retains the initial carrier while adding one fresh\nidentity at every step.', 'The one-step split is iterated without an ω-chain. The depths `k` and `n` are\narbitrary natural numbers. `DepthExtension k n` is a positive witness that\ndepth `n` was reached from depth `k`, and `IteratedCarrier I n` retains the\ninitial carrier while adding one fresh identity at every step. These laws are\nuniform in `n : Nat` and impose no maximum depth.'),
        ('both\ndirections of the finite index spoke and both directions of finite horizontal\ntransport', 'both\ndirections of the index spoke at that depth and both directions of horizontal\ntransport at that depth'),
        ('The\nrealized finite fresh identity is the one-step `fresh` identity', 'The\nfresh identity realized at depth one is the one-step `fresh` identity'),
        ('from its own finite birth depth', 'from its own natural-number birth depth, whatever that depth is'),
        ('Under finite readout extension, a distinction already\npresent at depth `k` persists at every supplied later depth.', 'Under readout extension to an arbitrary later natural-number depth, a distinction already\npresent at depth `k` persists at that depth.'),
    ],
    'Alignment/GenesisReconstruction.lean': [
        ('# Reconstruction of finite constitutive alignment', '# Reconstruction of constitutive alignment at arbitrary natural depth'),
        ('finite constitutive carriers', 'constitutive carriers indexed at an arbitrary natural depth'),
        ('fresh\nat a finite depth', 'fresh\nat a natural-number depth'),
        ('canonical finite old/fresh splits', 'canonical iterated old/fresh splits'),
        ('through the canonical finite\nold/fresh construction', 'through the canonical iterated\nold/fresh construction'),
        ('commutes with every canonical finite extension', 'commutes with every canonical extension between natural-number depths'),
        ('Every finite fresh-generation stratum is preserved by a transport.', 'Every fresh-generation stratum below the chosen natural depth is preserved by a transport.'),
    ],
    'Alignment/GenesisCharacterization.lean': [
        ('# Characterization of genesis-preserving finite transports', '# Characterization of genesis-preserving transports at arbitrary natural depth'),
        ('terminal exact transport between two finite constitutive carriers', 'terminal exact transport between two constitutive carriers at an arbitrary natural depth'),
        ('canonical finite lift', 'canonical lift to the chosen natural depth'),
        ('Exact finite transports', 'Exact transports at arbitrary natural depth'),
    ],
    'Alignment/GenesisRigidity.lean': [
        ('# Rigidity of genesis-preserving finite alignment', '# Rigidity of genesis-preserving alignment at arbitrary natural depth'),
        ('The finite genesis condition', 'The natural-depth genesis condition'),
        ('every supplied finite depth', 'every supplied natural-number depth'),
        ('Thus finite generation introduces no', 'Thus generation indexed by natural depth introduces no'),
        ('one finite depth', 'one natural-number depth'),
        ('every finite lift', 'every natural-depth lift'),
        ('every genesis-preserving finite transport', 'every genesis-preserving transport at that natural depth'),
        ('any finite depth', 'any natural-number depth'),
        ('any chosen finite depth', 'any chosen natural-number depth'),
    ],
    'Alignment/ConstitutiveProfileRigidity.lean': [
        ('for finite alignment', 'for alignment at arbitrary natural depth'),
        ('remaining finite alignment ambiguity', 'remaining natural-depth alignment ambiguity'),
        ('finite genesis reconstruction', 'genesis reconstruction at arbitrary natural depth'),
        ('from one\nfinite terminal candidate', 'from one\nterminal candidate at an arbitrary natural depth'),
        ('finite genesis-preserving alignment', 'genesis-preserving alignment at arbitrary natural depth'),
    ],
    'Alignment/ConstitutiveProfileReconstruction.lean': [
        ('canonical finite lift preserves genesis', 'canonical lift to every requested natural-number depth preserves genesis'),
        ('through finite constitutive depth', 'through an arbitrary natural-number constitutive depth'),
        ('Every finite transport reconstructed', 'Every transport reconstructed at a requested natural-number depth'),
        ('finite transport is the canonical lift', 'transport at that depth is the canonical lift'),
    ],
    'Alignment/AnchoredRelationReconstruction.lean': [
        ('every finite genesis-preserving lift', 'every lift to an arbitrary natural-number depth that preserves genesis'),
        ('Canonical finite alignment', 'Canonical alignment at any requested natural-number depth'),
    ],
    'Alignment/AnchoredMatchReconstruction.lean': [
        ('Canonical finite alignment reconstructed', 'Canonical alignment at an arbitrary requested natural-number depth reconstructed'),
        ('through every finite genesis depth', 'through every natural-number genesis depth'),
    ],
    'Alignment/FiniteAnchoredMatchSearch.lean': [
        ('exact transport, and finite genesis transport without an independently supplied resolver', 'exact transport, and genesis transport at any requested natural-number depth without an independently supplied resolver'),
    ],
    'Alignment/FiniteAlignmentClassification.lean': [
        ('Recover exact transport at a finite genesis depth only from the exact regime.', 'Recover exact transport at any requested natural-number genesis depth only from the exact regime.'),
    ],
    'Alignment/DirectionalGenesisPersistence.lean': [
        ('# Directional persistence through finite genesis', '# Directional persistence through arbitrary natural-depth genesis'),
        ('through the canonical finite old/fresh construction', 'through the canonical iterated old/fresh construction'),
        ('A forward-only finite alignment therefore persists as an injective\nfresh-preserving embedding at every finite depth', 'A forward-only alignment therefore persists as an injective\nfresh-preserving embedding for every `depth : Nat`'),
        ('every finite lift', 'every natural-depth lift'),
        ('at every finite depth', 'at every natural-number depth'),
        ('every finite fresh-generation stratum', 'every fresh-generation stratum below the chosen natural depth'),
        ('every canonical finite extension', 'every canonical extension between natural-number depths'),
        ('Witness-carrying finite directional embedding preserving genesis.', 'Witness-carrying directional embedding at an arbitrary natural depth, preserving genesis.'),
        ('The finite forward genesis embedding is canonical', 'The forward genesis embedding at any natural depth is canonical'),
        ('The finite backward genesis embedding is canonical', 'The backward genesis embedding at any natural depth is canonical'),
        ('Extract the finite forward genesis embedding', 'Extract the forward genesis embedding at the requested natural depth'),
        ('Extract the finite backward genesis embedding', 'Extract the backward genesis embedding at the requested natural depth'),
        ('reconstructed exact finite transport', 'reconstructed exact transport at that natural depth'),
        ('exact backward finite transport', 'exact backward transport at that natural depth'),
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

print('CORRECTED_FILES_BEGIN')
for name in changed:
    print(name)
print('CORRECTED_FILES_END')
print('MISSING_EXPECTED_BEGIN')
for filename, old in missing:
    print(f'{filename}: {old!r}')
print('MISSING_EXPECTED_END')

pattern = re.compile(r'(finite[- ]depth|finite persistence|finite extension|finite genesis|every finite depth|arbitrary finite depth|later finite depth|profondeur[s]? finie|persistance finie|extension finie|it[eé]ration finie|toute profondeur finie|profondeurs finies)', re.I)
print('RESIDUAL_DEPTH_WORDING_BEGIN')
for path in list(Path('.').rglob('*.md')) + list(Path('.').rglob('*.lean')):
    if '.lake' in path.parts:
        continue
    for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if pattern.search(line):
            print(f'{path}:{number}:{line}')
print('RESIDUAL_DEPTH_WORDING_END')
