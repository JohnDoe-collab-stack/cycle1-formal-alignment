# Fondements structurels — alignement relatif et réflexif

[English](README.md) | **Français**

> **Ce dépôt construit et vérifie en Lean un fondement constructif et
> dépendamment typé pour l'alignement relatif et réflexif.** Il démontre d'abord
> l'adéquation exacte entre un régime opérationnel et une norme définie
> indépendamment de ce régime sur les mêmes histoires constituées. À partir de
> cette adéquation établie, une branche construit une sortie opérationnelle
> minimale et fidèlement réalisable ; l'autre observe propositionnellement les
> deux familles de témoins, transporte leur équivalence dans une couche de
> représentation et démontre que la représentation exacte de ces statuts
> déterminés est compatible avec un statut diagonal construit hors de toute
> clôture réflexive globale de l'évaluateur.

## Architecture

```text
socle structurel
  constitution relationnelle
  → construction dépendamment typée
  → réalisation fidèle
  ↓
Cycle 1 — alignement relatif
  régime opérationnel et norme indépendante
  → transformation de témoins dans chaque sens
  → adéquation exacte
  ├── continuation minimale
  │     → sortie opérationnelle localisée
  │     → OOD structurel
  │
  └── observation propositionnelle par `Nonempty`
        → équivalence des deux statuts habités
        → tiré en arrière et transport vers les codes
        → représentation exacte de statuts déterminés
        + diagonalisation de l'évaluateur
        → statut diagonal non représentable
        → échec de la clôture réflexive globale
```

La bifurcation intervient après l'adéquation du Cycle 1. Le développement
diagonal ne découle pas de `oneStepAfterPerimeter`, et aucun théorème n'identifie
la sortie opérationnelle à la sortie représentationnelle.

## Cycle 1 — Alignement relatif

Pour une présentation circulaire `P` et une histoire générée enracinée `H`, le
Cycle 1 maintient trois familles de témoins distinctes :

```text
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

`F_A(H)` certifie la réalisation exacte dans une algèbre concrète fournie.
`R(H)` est l'admission par le régime opérationnel. `S(H)` est la satisfaction
d'une norme définie indépendamment de ce régime.

La preuve construit deux applications entre les types de témoins :

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

`circularNormativeAdequacy` définit l'adéquation comme une paire d'applications
dans ces deux sens, et `circularRefinement_adequateAlong` fournit cette paire à
chaque occurrence. Il ne s'agit ni d'une égalité ni d'un `Equiv` entre les
structures de témoins porteuses d'information de preuve.

Le candidat canonique

```text
h⁺ := oneStepAfterPerimeter P
```

est une continuation stricte du déploiement canonique. Il reste localement
exact, conserve la précédence et l'adjacence canoniques et possède une
`ExactConcreteRealization A h⁺` pour toute
`ConcreteContinuationAlgebra P` fournie. Pourtant, `R(h⁺)` et `S(h⁺)` sont tous
deux constructivement réfutés. La réfutation normative est directe : elle ne
déduit pas l'échec de la norme indépendante du seul rejet par le régime.

Les structures génériques `RegimeExit`, `UniformRegimeExit` et
`NormativeAdequacy` isolent l'architecture réutilisable. Les deux premières sont
polymorphes sur leur type porteur. L'interface normative actuelle est
paramétrique en norme et en régime, mais spécialisée à
`RootedGeneratedHistory P`.

## Cycle 2 — Alignement réflexif

Le Cycle 2 transforme d'abord les familles de témoins du Cycle 1 en propositions :

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

En utilisant les deux applications du Cycle 1, `circularStatusAdequacy` démontre :

```text
CircularRegimeStatus P H
  ↔ CircularSpecificationStatus P H
```

Ce `↔` est une équivalence d'habitabilité, non une équivalence entre les types
de témoins originaux. Après qu'un décodeur a tiré ces statuts en arrière vers
des prédicats sur les codes, la représentation exacte se transporte entre eux.

Indépendamment, pour tout évaluateur

```lean
eval : Code → Code → Prop
```

le noyau diagonal définit

```lean
diagonalStatus eval code := ¬ eval code code
```

et démontre constructivement qu'aucune ligne de `eval` ne représente exactement
ce prédicat. Un évaluateur de cette forme ne peut donc représenter tous les
prédicats sur son propre espace de codes.
`exactCircularStatusRepresentation_hasDiagonalOutside` combine les deux
résultats : le statut de régime choisi et le statut normatif équivalent sont
représentés exactement, tandis que le statut diagonal de l'évaluateur reste hors
de la représentabilité interne.

## Ce qui est établi

| Transition | Statut | Ancrage Lean principal |
|---|---|---|
| constitution → histoire | vérifié | `RootedGeneratedHistory` |
| rôles structurels → réalisation exacte | vérifié | `ExactNonClosingRealization` |
| histoire libre → réalisation concrète fidèle | vérifié | `exactlyInterpretHistory` |
| témoin de régime → témoin de norme | vérifié | `circularRefinement_soundSpecification` |
| témoin de norme → témoin de régime | vérifié | `circularSpecification_complete` |
| adéquation → équivalence propositionnelle des statuts | vérifié | `circularStatusAdequacy` |
| continuation → sortie opérationnelle | vérifié | `oneStepAfterPerimeter`, `RegimeExit` |
| statuts codés équivalents → représentation transportée | vérifié | `transportRepresentation` |
| évaluateur → statut diagonal non représentable | vérifié | `diagonalStatus_notRepresentable` |
| statut diagonal → échec de la clôture globale | vérifié | `noGlobalReflectiveClosure` |

La conséquence architecturale tirée de cette chaîne est distinguée des
théorèmes Lean : la clôture globale n'est pas seulement traitée comme un objectif
manqué, mais dépassée par une architecture dans laquelle la non-clôture est
constitutive, les frontières sont déterminées relativement à des régimes
explicites et la construction peut se poursuivre au-delà d'elles.

## Distinctions préservées

```text
construction ≠ réalisation fidèle
réalisation fidèle ≠ admission par un régime
régime ≠ norme indépendante
norme ≠ preuve d'adéquation
sortie opérationnelle ≠ sortie représentationnelle
diagonalisation abstraite ≠ théorèmes d'incomplétude de Gödel
résultat Lean ≠ conséquence dérivée ≠ interprétation architecturale
```

L'OOD structurel est proposé ici comme le cas d'un candidat constructible de
l'intérieur mais situé hors d'un régime opérationnel explicite. Il n'est
identifié ni à l'OOD statistique ni au désalignement relatif. Dans l'instance
circulaire, le même candidat porte en outre une réalisation exacte et une preuve
directe d'échec de la norme indépendante.

## Documentation

- [Fondements structurels](docs/fr/fondements_structurels.md) — synthèse
  canonique de l'architecture complète.
- [Cycle 1 — Alignement relatif](docs/fr/alignement_relatif.md) — preuve
  détaillée, signatures, adéquation et sortie opérationnelle.
- [Méthode des rôles constitutifs relationnels](docs/fr/methode_roles_constitutifs_relationnels.md)
  — protocole réutilisable de construction, séparation, reconstruction et audit.
- [Cycle 2 — Alignement réflexif](docs/fr/alignement_reflexif.md) —
  représentation exacte, diagonalisation et non-clôture globale.
- [Alignement constitutif des systèmes transformers](docs/fr/alignement_constitutif_transformers.md)
  — transposition architecturale de la constitution relationnelle à la mémoire
  persistante, au raisonnement à horizon long et aux sorties normatives
  localisées.
- [Compilation et audit axiomatique](audit/AUDIT_BUILD.txt) — relevé factuel
  reproductible.
- [Déclaration de conception](AI_AUTHORSHIP.md) — origine conceptuelle,
  provenance de génération par IA et historique du développement.

Les équivalents anglais sont liés en tête de chaque document scientifique.

## Architecture des sources

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) démontre le résultat
  abstrait sur l'occurrence résiduelle.
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) définit la
  classification exacte d'un régime et les sorties typées.
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) implémente la
  construction circulaire, la norme indépendante, l'adéquation relative et la
  sortie opérationnelle canonique.
- [`Cycle2/DiagonalizationKernel.lean`](Cycle2/DiagonalizationKernel.lean)
  implémente le noyau diagonal constructif abstrait en n'important que `Init`.
- [`Cycle2/ReflectiveAlignment.lean`](Cycle2/ReflectiveAlignment.lean) observe
  les statuts du Cycle 1 par `Nonempty` et transporte leur adéquation dans la
  couche de représentation.
- [`Cycle2.lean`](Cycle2.lean) est l'agrégateur public du Cycle 2, sans
  déclaration propre.

Aucun module du Cycle 1 n'importe le Cycle 2.

## Reproduction et audit

Avec `elan`, ou une installation équivalente lisant `lean-toolchain` :

```bash
lake clean
lake build
```

Vérifier le manifeste des sources scientifiques sous Linux ou macOS :

```bash
bash scripts/verify-manifest.sh
```

Sous Windows PowerShell :

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

La compilation épinglée construit les deux bibliothèques Lake, audite 325
déclarations au moyen des blocs finaux `#print axioms` et ne rapporte aucune
dépendance axiomatique. L'environnement exact, les décomptes, les empreintes et
les commandes sont consignés dans
[`audit/AUDIT_BUILD.txt`](audit/AUDIT_BUILD.txt).

## Portée, licence et citation

Le Cycle 1 est complet relativement à `CircularPresentation` ; ce n'est pas une
théorie universelle de toute norme ou de tout problème d'alignement. Le Cycle 2
est un argument diagonal sémantique abstrait, non une formalisation de la
syntaxe, de la prouvabilité, de l'arithmétisation ou des théorèmes
d'incomplétude de Gödel. Les deux cycles formels sont constructifs et n'emploient
ni `sorry`, ni `admit`, ni déclaration `axiom`, ni `Classical`, ni `propext`, ni
`Quot.sound`.

Le dépôt est un artefact autonome : aucun historique source privé n'est requis
pour le compiler ou l'auditer. Le code et la documentation sont distribués sous
licence Apache-2.0. Les métadonnées de citation figurent dans
[`CITATION.cff`](CITATION.cff).

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Chaque élément de ce dépôt a été écrit de
> A à Z par des modèles de la série ChatGPT d'OpenAI, sous direction humaine et
> au cours d'interactions successives. Voir la
> [déclaration bilingue complète](AI_AUTHORSHIP.md).
