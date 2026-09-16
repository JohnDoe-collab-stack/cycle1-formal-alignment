# Fondements structurels — alignement relatif et frontière représentationnelle

[English](README.md) | **Français**

> **Ce dépôt construit et vérifie en Lean un fondement constructif et
> dépendamment typé pour l'alignement relatif, accompagné d'un résultat autonome de frontière représentationnelle.** Il démontre d'abord
> l'adéquation exacte entre un régime opérationnel et une norme définie
> indépendamment de ce régime sur les mêmes histoires constituées. À partir de
> cette adéquation établie, une branche construit une sortie opérationnelle à
> une occurrence qui, comme toute histoire générée enracinée, admet une
> réalisation concrète exacte dans toute algèbre fournie ; l'autre observe
> propositionnellement les
> deux familles de témoins, transporte leur équivalence dans une couche de
> représentation et démontre que la représentation exacte de ces statuts
> déterminés est compatible avec un statut diagonal construit hors de la
> clôture représentationnelle globale de l'évaluateur.

## Unité théorique

L’unité théorique de ce projet n’est ni une couche particulière ni un résultat
final, mais la continuité démontrée d’une même détermination à travers plusieurs
couches distinctes et interdépendantes. Les rôles sont établis avant leurs
représentations, transportés sans fusion des couches, puis seulement ouverts à
des lectures indépendantes. Cette organisation impose une interprétation
globale des résultats locaux.

## Point d'entrée vérifié par la machine

[`StructuralEntrypoint.lean`](StructuralEntrypoint.lean) est le chemin le plus
court vers le résultat central du Cycle 1. Son théorème générique local vers
global montre qu'une réalisation locale exacte reconstruit le périmètre
canonique comme facteur initial de toute histoire générée enracinée ;
l'injectivité est dérivée de l'accord exact plutôt que supposée. Un deuxième
point d'entrée réunit le périmètre canonique, son adéquation opérationnelle et
normative, puis une continuation à une occurrence qui, comme toute histoire
générée enracinée, admet une réalisation concrète exacte dans toute algèbre
fournie et reste extérieure au régime comme à la spécification. Cette même
continuation instancie l’interface indépendante du contenu
`ExactOneStepConstitutiveAlignment` : son porteur d’occurrences se décompose
exactement entre les occurrences antérieures et une occurrence nouvelle,
tandis que chaque algèbre fournie en donne une réalisation exacte distincte de
ses porteurs. À ce niveau abstrait, cela n'affirme aucune préservation
indépendante des étiquettes, de l'ordre ou de la sémantique des pas ; l'instance
canonique démontre en outre que ses éléments ancien et nouveau induits sont les
occurrences concrètes natives. Les transports induits préservent les deux
parties et composent ponctuellement sans raccord pair à pair ajouté
indépendamment. Un troisième
expose l'habitant canonique d'un bus structurel dont les correspondances sont
mutuellement inverses ; l'interface elle-même n'affirme ni la canonicité ni
l'unicité de son habitant. Les lectures arbitraires ne sont branchées qu'après
la constitution de ce bus, indépendamment de leur type de valeurs. Deux
réalisations concrètes fournies sont coordonnées par les mêmes identités
périmétrales plutôt que par un raccord pair à pair supplémentaire ; on obtient
ainsi une co-indexation exacte et un reindexage sans perte des lectures, mais
aucune compatibilité sémantique automatique entre des valeurs fournies
indépendamment. Les deux transports sont ponctuellement indépendants de toute
réalisation intermédiaire.

Le résultat à un pas est aussi itéré sur le producteur réel du Cycle 1 à toute
profondeur finie. Chaque étape générée ajoute exactement une occurrence
nouvelle tout en conservant les occurrences antérieures. Le prolongement à
travers les étapes suivantes commute ponctuellement avec le changement de
réalisation concrète exacte, et les transports verticaux comme horizontaux sont
indépendants des étapes intermédiaires. Le prolongement vertical est aussi
ponctuellement indépendant du témoin proof-relevant `DepthExtension`, y compris
lorsque sa source et sa cible utilisent deux réalisations fournies distinctes.
À la profondeur un, les deux directions du transport horizontal, l'identité
nouvelle réalisée et l'application verticale `old` coïncident ponctuellement
avec l'interface à un pas antérieure. Les lectures restent en aval : un
exemple exécutable non constant conserve les valeurs `7` et `11` du périmètre,
puis les valeurs nouvelles `10`, `20` et `30`, à travers trois étapes dans les
réalisations libre et journalisée. Ce théorème fini ne formalise pas un
transformer et n'impose aucun accord entre des lectures fournies
indépendamment.

## Architecture

```text
socle structurel
  constitution relationnelle
  → construction dépendamment typée
  → réalisation fidèle
  ↓
Cycle 1 — alignement relatif
  régime opérationnel et norme indépendante
  → adéquation exacte
  → persistance finie / transport de réalisation / naturalité
  → continuation à une occurrence et sortie opérationnelle localisée

RepresentationBoundary.DiagonalizationKernel
  évaluateur → statut diagonal → non-représentabilité
  → échec de la clôture représentationnelle globale

adéquation Cycle 1 ──────────────────────────┐
                                             ├─→ RepresentationBoundary.CircularStatusRepresentation
DiagonalizationKernel ───────────────────────┘
  représentation exacte de statuts choisis
  + sortie diagonale de représentation
```

La continuation et l'alignement dynamique sont démontrés sans importer
`RepresentationBoundary`. Le noyau diagonal est autonome et n'importe que
`Init`. Le module de représentation des statuts circulaires constitue une
application séparée : il utilise l'adéquation propositionnelle déjà établie au
Cycle 1 avec le noyau diagonal. Aucun théorème n'identifie la sortie
opérationnelle à la sortie représentationnelle.

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

Dans cette instance du Cycle 1, `R(H)` et `S(H)` sont chacune habitées
exactement lorsque `H = perimeterDeployment P`. Elles sont donc coextensives
sur les histoires, bien que leurs types de témoins, leurs définitions et leurs
chemins de preuve restent distincts.

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
`ConcreteContinuationAlgebra P` fournie, comme toute histoire générée
enracinée. Une fois une telle algèbre fournie, la réalisation exacte est une
garantie uniforme de préservation, non une condition sélectionnant les
histoires ; l'obligation située en amont est de construire l'algèbre qui
satisfait l'interface. Pourtant, `R(h⁺)` et `S(h⁺)` sont tous deux
constructivement réfutés.
Ces réfutations sont relatives à la `CircularPresentation` fournie, en
particulier à son champ explicite `rejectInitialContraction`. La réfutation
normative est directe : elle ne déduit pas l'échec de la norme indépendante du
seul rejet par le régime.

Les structures génériques `RegimeExit`, `UniformRegimeExit` et
`NormativeAdequacy` isolent l'architecture réutilisable. Les deux premières sont
polymorphes sur leur type porteur. L'interface normative actuelle est
paramétrique en norme et en régime, mais spécialisée à
`RootedGeneratedHistory P`.

## Frontière représentationnelle

La branche de frontière représentationnelle n'est pas une deuxième étape de
l'alignement. Elle observe d'abord propositionnellement les familles de témoins
déjà établies au Cycle 1 :

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

À partir des deux applications du Cycle 1, `circularStatusAdequacy` démontre leur
équivalence propositionnelle. Après tiré en arrière par un décodeur vers des
prédicats sur les codes, `transportRepresentation` transporte la représentation
exacte le long de cette équivalence.

Indépendamment, `RepresentationBoundary.DiagonalizationKernel` définit, pour tout
évaluateur `eval : Code → Code → Prop`,

```lean
diagonalStatus eval code := ¬ eval code code
```

et démontre constructivement que ce prédicat n'est pas représentable
intérieurement. `noGlobalRepresentationClosure` réfute donc la représentation de
tout prédicat sur le propre espace de codes de l'évaluateur.

`localExactRepresentation_hasDiagonalExit` combine ces deux faits indépendants :
le statut de régime circulaire choisi et son statut normatif équivalent sont
représentés exactement, tandis que le statut diagonal de l'évaluateur demeure
hors de la représentabilité interne.

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
| statut diagonal → échec de la clôture globale | vérifié | `noGlobalRepresentationClosure` |

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
- [Frontière représentationnelle](docs/fr/frontiere_representationnelle.md) —
  représentation exacte locale, diagonalisation et non-clôture représentationnelle globale.
- [Compilation et audit axiomatique](audit/AUDIT_BUILD.txt) — relevé factuel
  reproductible.
- [Déclaration de conception](AI_AUTHORSHIP.md) — origine conceptuelle,
  provenance de génération par IA et historique du développement.

Les équivalents anglais sont liés en tête de chaque document scientifique.

## Architecture des sources

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) isole les
  dépendances consommées par le résultat abstrait sur l'occurrence résiduelle,
  caractérise la reconstruction exacte et conserve l'interface riche existante.
- [`SegmentedResidualRoleStrictness.lean`](SegmentedResidualRoleStrictness.lean)
  fournit un séparateur positif : le noyau faible produit son occurrence
  résiduelle unique alors qu'aucune réalisation interne exacte n'existe sur les
  types du séparateur.
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) définit la
  classification exacte d'un régime et les sorties typées.
- [`ExactTypeTransport.lean`](ExactTypeTransport.lean) isole les transports
  exacts constructifs à deux inverses, indépendamment du contenu du Cycle 1.
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) implémente la
  construction circulaire, la norme indépendante, l'adéquation relative et la
  sortie opérationnelle canonique.
- [`Alignment/Constitutive.lean`](Alignment/Constitutive.lean) définit
  l'alignement exact à un pas indépendant du contenu, puis dérive la naturalité,
  la cohérence des chemins et l'unicité ponctuelle relative.
- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean)
  dérive la persistance verticale finie, le transport horizontal entre
  réalisations et leur carré commutatif depuis un même indice constitutif.
- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)
  attache ensuite les lectures finies et prouve la persistance de toute
  distinction qu'elles établissent déjà.
- [`Cycle1/ConstitutivePersistence.lean`](Cycle1/ConstitutivePersistence.lean)
  construit la persistance canonique à un pas et instancie l'alignement abstrait
  en maintenant séparés l'admission et le statut relatif à la spécification.
- [`Cycle1/IteratedConstitutivePersistence.lean`](Cycle1/IteratedConstitutivePersistence.lean)
  instancie la persistance finie avec les histoires réellement produites par
  `generate`/`appendGenerated` et leurs occurrences libres et concrètes natives.
- [`Examples/Alignment/IteratedReadout.lean`](Examples/Alignment/IteratedReadout.lean)
  calcule et démontre une lecture non constante à travers trois étapes générées
  et deux réalisations concrètes distinctes.
- [`Examples/ConcreteContinuation/LoggedAlgebra.lean`](Examples/ConcreteContinuation/LoggedAlgebra.lean)
  fournit une `ConcreteContinuationAlgebra` constructive, observable et non
  identitaire, sans devenir une dépendance du fondement structurel ni de la
  façade.
- [`RepresentationBoundary/DiagonalizationKernel.lean`](RepresentationBoundary/DiagonalizationKernel.lean)
  implémente le noyau diagonal constructif abstrait en n'important que `Init`.
- [`RepresentationBoundary/CircularStatusRepresentation.lean`](RepresentationBoundary/CircularStatusRepresentation.lean)
  applique la frontière représentationnelle aux statuts propositionnels circulaires.
- [`RepresentationBoundary.lean`](RepresentationBoundary.lean) est l'agrégateur
  public sans déclaration propre de cette branche.

Aucun module `Alignment/*` ou `Cycle1/*` n'importe `RepresentationBoundary`.

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

Sous Windows, avec PowerShell 7 :

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

ou avec Windows PowerShell :

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

`MANIFEST.sha256` couvre les sources Lean publiées et les documents
scientifiques canoniques qu'il énumère. Les métadonnées du dépôt et les
documents d'accès, dont les présents README, sont extérieurs à ce manifeste des
sources scientifiques. Plus précisément, le manifeste ne protège pas par
empreinte `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, le workflow
CI, `audit/AUDIT_BUILD.txt`, le manifeste lui-même
ni les deux README. Leur identité est donc fixée par le commit Git audité, et
non par `MANIFEST.sha256`.

Chaque fichier Lean se termine par un bloc explicite `#print axioms` pour ses
déclarations principales. La bibliothèque de production et la bibliothèque de
régression constructive se compilent avec :

```bash
lake build
lake build AuditRegression
```

## Portée, licence et citation

Le Cycle 1 est complet relativement à `CircularPresentation` ; ce n'est pas une
théorie universelle de toute norme ou de tout problème d'alignement.
`RepresentationBoundary` est un argument diagonal sémantique abstrait autonome,
non une formalisation de la syntaxe, de la prouvabilité, de l'arithmétisation ou
des théorèmes d'incomplétude de Gödel. Les déclarations sources des deux branches
sont constructives et
n'emploient ni `sorry`, ni `admit`, ni déclaration `axiom`, ni déclaration
`noncomputable`, ni `Classical`, ni `propext`, ni `Quot.sound`. Les blocs
`#print axioms` placés à la fin des fichiers sources n'établissent aucune
dépendance axiomatique pour les déclarations qu'ils nomment.

Le dépôt est un artefact autonome : aucun historique source privé n'est requis
pour le compiler ou l'inspecter. Le code et la documentation sont distribués sous
licence Apache-2.0. Les métadonnées de citation figurent dans
[`CITATION.cff`](CITATION.cff).

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Chaque élément de ce dépôt a été écrit de
> A à Z par des modèles de la série ChatGPT d'OpenAI, sous direction humaine et
> au cours d'interactions successives. Voir la
> [déclaration bilingue complète](AI_AUTHORSHIP.md).
