# Cartographie architecturale vérifiée

## Statut

Ce document fixe la cartographie architecturale de référence du dépôt à partir
de l'état validé de la branche `research/mediated-transition-coherence`, commit
`384f336aa0255776b982cc34c5c9fd6cde83d9fa`.

Il distingue explicitement :

1. la **lignée scientifique** qui mène à l'instance circulaire du projet ;
2. le **DAG technique des imports Lean**, qui contient plusieurs racines
   abstraites indépendantes ;
3. les **raccords** où une théorie générique est appliquée à l'instance
   circulaire ;
4. les branches de **validation**, d'**exemple** et de **régression**, qui ne
   constituent pas de nouvelles étapes de la théorie.

En cas de divergence entre un ancien diagramme narratif et ce document, cette
cartographie prévaut pour interpréter l'architecture du code. Elle ne prescrit
pas encore un renommage de fichiers : elle fixe d'abord les relations
scientifiques et techniques que tout refactor doit préserver.

## 1. Lignée scientifique de la circularité

Le tronc scientifique propre à la circularité est :

```text
SegmentedResidualRole
        |
        v
AbstractSegmentedTurning
        |
        v
StrongPerimetralTurning
        |
        v
instance du projet : circularité / périmètre
```

### `SegmentedResidualRole`

`SegmentedResidualRole.lean` est le premier noyau abstrait de cette lignée. Il
importe seulement `Init` et isole la détermination d'un rôle résiduel et
l'unicité de l'occurrence nouvelle. Il ne dépend d'aucune présentation
circulaire, différence, provenance, boucle, jonction ou totalisation.

La branche :

```text
SegmentedResidualRole
        |
        +----> SegmentedResidualRoleStrictness
```

est une branche de **validation de stricteté**. Elle montre constructivement
que le noyau résiduel faible peut être habité alors qu'une interface interne
plus riche n'est pas reconstructible. Elle n'est pas une étape productive vers
l'instance circulaire.

### `AbstractSegmentedTurning`

`AbstractSegmentedTurning.lean` importe `SegmentedResidualRole` et construit le
turning abstrait d'une totalité segmentée : générateur de frontière,
classification exacte du régime, continuation stricte, sortie de régime et
rejet des tentatives de totalisation.

Le théorème de production fondamental est `coreTurning`. Sa signature consomme
la frontière résiduelle minimale et un régime obstrué ; elle ne contient aucune
notion de circularité.

### `StrongPerimetralTurning`

`StrongPerimetralTurning.lean` importe `AbstractSegmentedTurning` et
`ExactTypeTransport`. C'est **l'instance scientifique du projet**, c'est-à-dire
l'instance circulaire/périmétrale.

C'est ici qu'apparaissent notamment `CircularPresentation`, `PerimeterSpine`,
`NonClosingPosition`, les histoires générées, les obstructions de fermeture,
les raffinements circulaires, la spécification circulaire et les réalisations
concrètes.

Le chemin de production utilise effectivement le noyau abstrait :

```text
oneStepResidualDeterminationCore
        |
        v
oneStepCoreResidualOccurrence
        |
        v
oneStepCoreSegmentedBoundary
        |
        v
perimetralCoreCoupledRegime
        |
        v
perimetralCoreObstructedRegime
        |
        v
oneStepCoreTurning
        |
        v
AbstractSegmentedTurning.coreTurning
        |
        v
abstractTurningOfCircularPresentation
```

Ainsi, la séquence

```text
résidu abstrait -> turning abstrait -> instance circulaire
```

est à la fois une lecture scientifique et un chemin de preuve réellement
utilisé dans le code de production.

## 2. Le DAG technique n'est pas une chaîne unique

La lignée précédente ne doit pas être confondue avec l'ensemble du graphe
d'imports. Trois autres noyaux abstraits sont indépendants de la circularité.

### `ExactTypeTransport`

`ExactTypeTransport.lean` définit des transports exacts constructifs par deux
applications et leurs deux lois de round-trip. Il est indépendant de toute
constitution, réalisation, admission, spécification ou lecture.

Il est utilisé directement par `StrongPerimetralTurning`, et sert aussi de
racine à la théorie générique d'alignement :

```text
ExactTypeTransport
        |
        v
Alignment.Constitutive
        |
        v
Alignment.FinitePersistence
        |
        v
Alignment.ReadoutPersistence
```

`Alignment.Constitutive` précise qu'il isole une structure indépendante du
contenu, extraite de la preuve canonique de persistance à un pas. Il faut donc
distinguer :

- la **lignée d'extraction scientifique** : l'interface d'alignement a été
  extraite d'une construction canonique ;
- la **dépendance Lean actuelle** : le module abstrait ne dépend plus de
  l'instance circulaire.

`Alignment.FinitePersistence` ajoute la profondeur finie, les extensions et les
transports par indice constitutif. `Alignment.ReadoutPersistence` attache les
lectures seulement après constitution et réalisation.

### `MediatedTransitionCoherence`

`MediatedTransitionCoherence.lean` importe seulement `Init`. Il formalise un
noyau constructif autonome de commutation par médiateur, de composition des
réalisations et de collage de carrés adjacents.

L'application actuelle à l'alignement fini est :

```text
MediatedTransitionCoherence
             +
Alignment.FinitePersistence
             |
             v
Cycle1/MediatedTransitionCoherence.lean
             |
             v
Cycle1/MediatedTransitionPasting.lean
```

Malgré leur chemin actuel sous `Cycle1/`, ces deux modules sont génériques sur
`FiniteConstitutiveAlignment`. Ils ne dépendent pas de `CircularPresentation`
ni de l'instance circulaire de `StrongPerimetralTurning`.

Leur emplacement actuel est donc un fait historique du système de fichiers,
pas une dépendance scientifique à un « Cycle 1 ».

### `RepresentationBoundary.DiagonalizationKernel`

`RepresentationBoundary/DiagonalizationKernel.lean` importe seulement `Init`.
Il définit indépendamment la représentabilité interne, le statut diagonal,
l'échec de la clôture représentationnelle globale et la sortie diagonale.

Ce noyau n'est pas une conséquence de l'alignement.

### Namespace et spécialisation

Plusieurs structures génériques (`ExactTypeTransport`, `Alignment/*`,
`MediatedTransitionCoherence`) vivent actuellement sous le namespace Lean
`StrongPerimetralTurning`. Cette appartenance nominale **ne suffit pas** à les
classer comme spécialisations circulaires. Leur niveau de spécialisation doit
être déterminé par leurs imports et leurs signatures.

## 3. Raccord de l'alignement à l'instance circulaire

Le raccord canonique à un pas est actuellement contenu dans
`Cycle1/ConstitutivePersistence.lean`.

Ses imports sont exactement :

```lean
import StrongPerimetralTurning
import Alignment.Constitutive
```

et son namespace mathématique est :

```text
StrongPerimetralTurning.ConstitutivePersistence
```

Sa fonction est de prendre la continuation réellement construite par l'instance
circulaire et de l'exposer à travers l'interface abstraite
`ExactOneStepConstitutiveAlignment`.

Le raccord n'invente pas une deuxième identité nouvelle. Le théorème
`canonicalAlignment_fresh_eq_residualFreeOccurrence` établit que l'identité
`fresh` de l'alignement canonique est exactement l'occurrence résiduelle libre
de l'instance circulaire. Le théorème
`canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence` établit le
même accord dans toute réalisation concrète fournie.

Le schéma correct est donc :

```text
StrongPerimetralTurning ---------+
                                 |
                                 v
                    ConstitutivePersistence
                                 ^
                                 |
Alignment.Constitutive ----------+
```

## 4. Persistance finie de l'instance circulaire

`Cycle1/IteratedConstitutivePersistence.lean` importe
`Alignment.ReadoutPersistence` et `Cycle1.ConstitutivePersistence`.

Il construit réellement les histoires finies de l'instance :

```text
iteratedHistory 0
  = perimeterDeployment

iteratedHistory (n + 1)
  = appendGenerated previous (generate previous.endpoint)
```

puis les expose comme `FiniteConstitutiveAlignment` et comme réalisations
exactes. Cette couche démontre ensuite la persistance des identités, les
transports entre réalisations, la naturalité et la persistance de l'occurrence
résiduelle opérationnelle.

Le rôle architectural est :

```text
ConstitutivePersistence + Alignment.ReadoutPersistence
                         |
                         v
           IteratedConstitutivePersistence
```

La lecture est « persistance finie de l'instance circulaire », et non
« deuxième constitution de la circularité ».

## 5. Branche représentationnelle

L'application circulaire de la frontière représentationnelle est
`RepresentationBoundary/CircularStatusRepresentation.lean`.

Ses imports sont exactement :

```lean
import StrongPerimetralTurning
import RepresentationBoundary.DiagonalizationKernel
```

Elle observe propositionnellement les statuts déjà établis dans l'instance :

```text
CircularRegimeStatus
  = Nonempty (CircularRefinement ...)

CircularSpecificationStatus
  = Nonempty (CircularSpecificationSatisfaction ...)
```

et obtient leur adéquation à partir de
`circularRefinement_soundSpecification` et `circularSpecification_complete`.

Le raccord est donc direct :

```text
StrongPerimetralTurning --------------------+
                                            |
                                            v
                         CircularStatusRepresentation
                                            ^
                                            |
DiagonalizationKernel ----------------------+
```

Il n'existe aucune dépendance de cette branche vers
`ConstitutivePersistence`, `IteratedConstitutivePersistence` ou `Alignment/*`.

Inversement, l'alignement dynamique et la persistance ne dépendent pas de
`RepresentationBoundary`.

La sortie opérationnelle et la sortie représentationnelle restent donc deux
diagnostics distincts.

## 6. Façade, exemples et régressions

`StructuralEntrypoint.lean` importe actuellement
`Cycle1.IteratedConstitutivePersistence`. Il constitue une façade humaine sur
la branche de persistance de l'instance ; il n'importe pas
`RepresentationBoundary`.

Les fichiers `Examples/*` fournissent des réalisations et lectures concrètes en
aval. Ils ne constituent pas les noyaux abstraits.

Les fichiers `Tests/*` sont des régressions et séparateurs. Ils peuvent
re-dériver indépendamment des propriétés de production, mais ne sont pas des
dépendances des modules de production.

## 7. Cartographie canonique

La vue canonique doit être lue par blocs, sans imposer une chronologie totale :

```text
LIGNEE SCIENTIFIQUE DE LA CIRCULARITE

SegmentedResidualRole
   |\
   | +--> SegmentedResidualRoleStrictness   [validation]
   |
   v
AbstractSegmentedTurning
   |
   v
StrongPerimetralTurning                     [instance = circularité]


INFRASTRUCTURE GENERIQUE D'ALIGNEMENT

ExactTypeTransport
   |
   v
Alignment.Constitutive
   |
   v
Alignment.FinitePersistence
   |
   v
Alignment.ReadoutPersistence


RACCORD A L'INSTANCE CIRCULAIRE

StrongPerimetralTurning + Alignment.Constitutive
   |
   v
ConstitutivePersistence

ConstitutivePersistence + Alignment.ReadoutPersistence
   |
   v
IteratedConstitutivePersistence


COHERENCE MEDIEE GENERIQUE

MediatedTransitionCoherence + Alignment.FinitePersistence
   |
   v
finite mediated coherence
   |
   v
mediated pasting


FRONTIERE REPRESENTATIONNELLE

DiagonalizationKernel + StrongPerimetralTurning
   |
   v
CircularStatusRepresentation


FACADE

IteratedConstitutivePersistence
   |
   v
StructuralEntrypoint
```

## 8. Invariants architecturaux figés

Tout futur refactor de noms ou de chemins doit préserver les invariants
suivants :

- `SegmentedResidualRole` précède abstraitement le turning segmenté ;
- `SegmentedResidualRoleStrictness` reste une branche de validation, non une
  étape productive ;
- `AbstractSegmentedTurning` reste indépendant de la circularité ;
- `StrongPerimetralTurning` est l'instance circulaire/périmétrale du projet ;
- l'occurrence résiduelle consommée par le turning et l'identité fraîche de
  l'alignement canonique sont reliées par des théorèmes d'accord explicites ;
- `ExactTypeTransport` reste une infrastructure générique partagée ;
- la théorie `Alignment/*` reste générique et n'est pas autorisée à constituer
  rétroactivement l'occurrence résiduelle ;
- les lectures restent en aval de la constitution et de la réalisation ;
- `MediatedTransitionCoherence` reste un noyau générique indépendant ;
- l'application de cohérence médiée à `FiniteConstitutiveAlignment` ne doit pas
  être interprétée comme spécifique à la circularité ;
- `DiagonalizationKernel` reste autonome ;
- `CircularStatusRepresentation` se raccorde directement aux statuts de
  `StrongPerimetralTurning` et au noyau diagonal ;
- aucune dépendance ne doit faire de `RepresentationBoundary` une étape
  nécessaire de l'alignement dynamique ;
- aucune dépendance ne doit faire de l'alignement une condition préalable au
  turning résiduel de l'instance circulaire.

## 9. Statut du nom `Cycle1`

À l'état de référence, `Cycle1` est encore un chemin de fichiers et un nom de
cible Lake. Cette cartographie **ne le traite pas comme un nœud mathématique
canonique**, car les quatre fichiers actuellement placés sous `Cycle1/` ne
forment pas une seule classe conceptuelle :

- `ConstitutivePersistence.lean` et
  `IteratedConstitutivePersistence.lean` sont des développements de l'instance
  circulaire ;
- `MediatedTransitionCoherence.lean` et
  `MediatedTransitionPasting.lean` sont des spécialisations génériques de
  `FiniteConstitutiveAlignment`.

Ce constat est figé. Le choix éventuel de nouveaux chemins ou noms est une
décision de refactor séparée et ne fait pas partie du présent document.
