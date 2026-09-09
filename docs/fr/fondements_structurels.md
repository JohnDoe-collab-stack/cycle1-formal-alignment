# Cycle 1 — Fondements structurels

*De la constitution relationnelle à l'alignement relatif*

[English](../en/structural_foundations.md) | **Français**

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d'OpenAI, sous direction humaine et au cours
> d'interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).

> **Ce document expose le cadre conceptuel qui rend possible la preuve formelle
> d'alignement relatif du cycle 1.** Son principe directeur est de préserver
> l'individuation la plus fine et les relations qui la constituent, puis de ne
> projeter, classifier, quotienter ou mesurer qu'après avoir démontré que
> l'information oubliée n'est pas nécessaire à la détermination considérée.

La preuve complète de soundness, de carrier completeness et de regime
completeness est présentée séparément:

- [preuve formelle — français](preuve_formelle_alignement_relatif.md);
- [formal proof — English](../en/formal_relative_alignment_proof.md).

## Statut des énoncés

Ce document distingue trois statuts afin de ne pas confondre preuve et
interprétation:

| Statut | Signification |
|---|---|
| **Vérifié dans Lean** | définition, construction ou théorème nommé dans les modules du cycle 1 |
| **Conséquence dérivée** | composition explicite de résultats Lean déjà vérifiés |
| **Proposition conceptuelle** | vocabulaire ou lecture théorique introduite par la documentation |

Les quatre distinctions sont des principes structurants réalisés et contrôlés
dans l'application périmétrale. Elles ne sont pas revendiquées comme quatre
théorèmes universels indépendants. La notion d'OOD structurel introduite plus bas
est une proposition conceptuelle; elle n'est pas encore une définition Lean.

## 1. Les quatre distinctions

### 1.1 L'individuation précède définitionnellement l'identité

Les constitutions sont construites avec leurs formations. Leurs lectures sont
ensuite extraites sans servir de définition à leur identité.

Pour une lecture:

```text
ρ : O → V
```

l'égalité:

```text
ρ(x) = ρ(y)
```

n'impose pas en général:

```text
x = y
```

Les formations, provenances, positions et rôles peuvent ainsi rester distingués
lorsque certaines lectures coïncident. La primauté de l'individuation ne supprime
pas l'égalité dans le type des occurrences; elle interdit seulement de définir
rétroactivement cette individuation par une lecture extensionnelle.

### 1.2 La totalité est locale et ne se confond pas avec la globalité

Une réalisation peut satisfaire exactement toutes les exigences d'un périmètre
sans épuiser les constructions possibles au-delà. Une localité totale relativement
à ses exigences n'est donc pas une maximalité dans l'espace des constructions.

Cette distinction rend intelligible le résultat central de l'application
circulaire:

```text
déploiement périmétral complet localement
  +
continuation libre effectivement constructible
```

### 1.3 La succession est indexée par une localité totale

Dans la réalisation périmétrale, les pas générés dépendent de la présentation et
de la constitution source. Aucune horloge extérieure n'est requise pour définir
leur succession.

### 1.4 Le temps et le global sont dérivés de la trajectoire

Les histoires composent les pas. Leurs préfixes définissent une antériorité
structurelle. Le temps désigne ici cette antériorité et le global l'histoire
composée, relativement à la présentation donnée.

Les quatre distinctions forment donc un ordre de dépendance:

```text
présentation
→ localité et rôles
→ occurrences formées et réalisation locale
→ succession
→ histoire
```

Puis:

```text
histoire → antériorité des préfixes → temps
histoire → composition              → global
histoire → interprétation concrète  → lectures
```

Une lecture ne constitue pas l'occurrence qu'elle lit. Une totalité locale ne
constitue pas une globalité. Une histoire n'est pas indexée par une horloge
extérieure. Le temps et le global sont obtenus à partir de sa structure.

## 2. La méthode des rôles constitutifs relationnels

La méthode consiste à déterminer une occurrence par sa constitution et par les
relations auxquelles elle participe avant de la réduire à une lecture, une
classification ou une valeur.

```text
individuation
→ formation
→ occurrence
→ rôle relationnel
→ succession et composition
→ invariants
→ lectures et classifications
```

Cet ordre interdit plusieurs identifications prématurées:

```text
même lecture
≠ même occurrence

même rôle
≠ même occurrence sans fidélité supplémentaire

être positionné entre deux occurrences
≠ participer à leur composition constitutive

être admis par un régime
≠ satisfaire une spécification indépendante
```

### 2.1 Réaliser exactement un rôle

Une localité fournit des rôles ou des exigences à réaliser. Réaliser un rôle ne
consiste pas seulement à attribuer une étiquette. Il faut établir un accord
structurel entre l'occurrence effectivement constituée et le rôle requis.

Dans l'application périmétrale, `RequirementOccurrenceAgreement` impose l'égalité
exacte entre le `LocatedStep` d'une occurrence et le pas canonique correspondant
à une `NonClosingPosition`.

```text
rôle requis
+ occurrence individuée
+ accord structurel exact
```

Les accords sur la source, la cible, la compatibilité et la provenance sont
ensuite dérivés de cet accord plus fin.

### 2.2 Couverture exacte sans exhaustivité

`ExactNonClosingRealization` fournit:

```text
pour chaque exigence non fermante
  une occurrence qui la réalise exactement

pour deux exigences distinctes
  deux occurrences distinctes
```

Il n'affirme pas que ces occurrences épuisent toute l'histoire. Une histoire peut
donc réaliser exactement toutes les exigences requises tout en comportant des
occurrences supplémentaires.

```text
couverture exacte des exigences
≠ classification exhaustive des occurrences
```

### 2.3 Ordre et adjacence dérivés dans l'histoire réelle

L'exactitude locale prise sur un carrier affaibli ne détermine pas à elle seule
l'ordre ou l'adjacence. Dans une véritable `RootedGeneratedHistory`, la
composabilité permet cependant de les reconstruire:

```lean
ExactNonClosingRealization.preservesPrecedence
ExactNonClosingRealization.preservesNext
```

Ces théorèmes établissent respectivement la précédence canonique et l'adjacence
constitutive canonique des occurrences réalisées.

```text
ExactNonClosingRealization
+ RootedGeneratedHistory
→ précédence correcte
+ adjacence constitutive correcte
```

Le statut local est donc:

```text
ExactNonClosingRealization   primitive locale
précédence                   dérivée
adjacence                    dérivée
participation                portée par History
contiguïté pertinente        dérivée
```

## 3. Minimiser les primitives par des modèles séparateurs

La méthode ne consiste pas à accumuler les primitives, mais à déterminer celles
qui sont réellement indépendantes. Le développement utilise pour cela des
carriers affaiblis et des modèles séparateurs.

`SemanticTrace` conserve des `GeneratedStep` localement valides et des occurrences
individuées, mais retire la composabilité globale imposée par `History`.

### 3.1 Trace permutée

```text
p2, p1, p3
```

Cette trace admet une réalisation locale exacte et injective tout en inversant
les deux premières exigences. L'exactitude locale ne détermine donc pas seule
l'ordre. `NonClosingPrecedes` et `SemanticOrderPreserved` représentent cette
propriété séparément sur le carrier affaibli.

### 3.2 Trace intercalée

```text
p1, extra1, p2, extra2, p3
```

Cette trace conserve l'exactitude locale et l'ordre, mais contient des occurrences
supplémentaires entre les réalisations canoniques. Elle montre que la position
intermédiaire ne détermine pas la participation à une composition constitutive.

`SemanticTrace.Between` décrit la position. `ExactSemanticBridgeSegment` demande
en plus une correspondance exacte avec les occurrences d'une `GeneratedHistory`
qui constituerait réellement le pont. Les théorèmes sur l'exemple intercalé
réfutent l'existence d'un tel pont entre deux exigences canoniquement
adjacentes.

```text
position intermédiaire
≠ participation à la composition constitutive
```

La contiguïté pertinente n'est donc pas primitive. Elle peut être dérivée de
l'adjacence constitutive et de l'irréflexivité de la génération.

### 3.3 Procédure de minimisation

```text
1. proposer une détermination candidate
2. affaiblir le carrier sans détruire les notions déjà établies
3. chercher un modèle conservant les couches plus faibles
   tout en violant la propriété candidate
4. décider si cette violation doit être admise ou rejetée
5. si la propriété est nécessaire, l'introduire au niveau minimal
6. réintroduire la composition réelle
7. vérifier si la propriété devient alors dérivable
8. ne conserver comme primitives que les déterminations non reconstruites
```

L'absence de contre-modèle dans un langage de construction déjà trop contraint
ne suffit pas à établir qu'une propriété est primitive.

## 4. Rôles constitutifs relationnels

Un **rôle constitutif relationnel** est le rôle d'une occurrence déterminé
par les relations structurelles dans lesquelles elle intervient au sein d'une
constitution.

Le terme *constitutif* indique que le rôle n'est pas une classification
extérieure ajoutée après coup. Le terme *relationnel* indique qu'il ne se réduit
pas à une propriété isolée de l'occurrence.

Une occurrence peut être déterminée simultanément par:

```text
sa formation
sa provenance
sa source et sa cible
sa place dans une succession
son rôle relativement à une localité
sa participation à une composition
```

sans qu'une lecture soit autorisée à redéfinir rétroactivement son individuation.

Le principe méthodologique stabilisé est:

> **Préserver l'individuation la plus fine et les relations qui la constituent,
> puis ne projeter, classifier, quotienter ou mesurer qu'après avoir démontré que
> l'information oubliée n'est pas nécessaire à la détermination considérée.**

## 5. Mesure structurelle et conservation exacte

Le terme **mesure structurelle** ne désigne pas ici une mesure sigma-additive sur
une algèbre d'ensembles. Il désigne la détermination exacte portée par les
occurrences, leurs correspondances et leurs indexations avant toute évaluation
numérique.

### 5.1 Détermination cardinale avant calcul

Sous les conditions de fidélité définies,
`positiveContinuation_exactlyOne` démontre qu'une continuation positive comporte
exactement une occurrence. La preuve établit d'abord l'existence et l'unicité;
la valeur numérique `1` peut ensuite être lue comme invariant.

```text
structure relationnelle
→ existence et unicité
→ invariant cardinal
→ lecture numérique 1
```

La composition est elle aussi structurelle. `History.append` raccorde les
histoires tout en distinguant les occurrences provenant de chacune.

### 5.2 Conservation dans les réalisations concrètes

Pour toute `ConcreteContinuationAlgebra P` fournie, `exactlyInterpretHistory`
construit deux correspondances inverses entre les occurrences de l'histoire libre
et celles de sa réalisation concrète. Les aller-retours restituent exactement les
occurrences de départ.

```text
occurrences libres ⇄ occurrences concrètes
```

`ConcreteOccurrenceAgreement` relie en outre chaque occurrence aux sources,
cibles et pas qu'elle interprète. Dans l'interface considérée, cela exclut la
perte, la fusion ou l'ajout d'une occurrence sans correspondant.

La conservation est donc plus riche qu'une égalité de cardinalités. Elle porte
sur une équivalence d'occurrences accompagnée des accords structurels spécifiés.

Il s'ensuit que deux réalisations concrètes fournies pour une même histoire
conservent la même détermination d'occurrences, chacune étant reliée exactement à
l'histoire libre commune. Cette phrase est une conséquence dérivée des deux
interprétations exactes, et non le nom d'un théorème binaire supplémentaire.

```text
structure d'occurrences conservée
⇒ invariants structurels et quantitatifs
⇒ lectures numériques
```

## 6. Application circulaire et alignement relatif

L'application circulaire relie les trois modules:

- [`SegmentedResidualRole.lean`](../../SegmentedResidualRole.lean) établit le résultat
  abstrait sur les occurrences résiduelles;
- [`AbstractSegmentedTurning.lean`](../../AbstractSegmentedTurning.lean) le raccorde à
  la classification et à la sortie d'un régime;
- [`StrongPerimetralTurning.lean`](../../StrongPerimetralTurning.lean) construit les
  histoires, le périmètre, les interprétations et l'instance d'alignement.

Elle distingue la compatibilité d'une jonction, l'identification des extrémités
et la continuation effectivement produite. Dans l'exemple à quatre nœuds, la
jonction du quatrième vers le premier est compatible, mais le pas généré produit
une constitution au-delà du périmètre.

### 6.1 Norme indépendante et régime

Pour une histoire `H`:

```text
F_A(H) := ExactConcreteRealization A H
S(H)   := CircularSpecificationSatisfaction P H
R(H)   := CircularRefinement P H
```

La norme est une structure à deux champs:

```text
CircularSpecificationSatisfaction P H
  ├─ local : ExactNonClosingRealization P H
  └─ trajectory :
       StrictConstitutivePrefix (perimeterDeployment P) H
       → P.TotalLoop
```

La preuve formelle établit:

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

Le régime et la norme classent exactement les mêmes histoires sans identifier
leurs structures de témoins.

### 6.2 Contraste canonique

| Propriété | `perimeterDeployment P` | `oneStepAfterPerimeter P` |
|---|---:|---:|
| réalisation locale exacte | ✓ | ✓ |
| précédence correcte | ✓ | ✓ |
| adjacence constitutive correcte | ✓ | ✓ |
| réalisation concrète exacte pour toute algèbre fournie | ✓ | ✓ |
| `CircularSpecificationSatisfaction` | ✓ | ✗ |
| `CircularRefinement` | ✓ | ✗ |

`oneStepAfterPerimeter P` est un contre-exemple canonique, pas un modèle de la
norme. Il reste constructible et fidèlement réalisable, mais échoue précisément
sur l'obligation trajectorielle.

```text
capacité à continuer
≠ admission normative

fidélité locale
≠ alignement trajectoriel global
```

### 6.3 Sortie typée et adéquation

`RegimeExit` est polymorphe sur un carrier arbitraire. Il réunit:

```text
candidate
faithful : Faithful candidate
inadmissible : Regime candidate → False
```

`UniformRegimeExit` fixe le candidat avant la variation des implémentations et
demande sa fidélité dans chacune des implémentations fournies.
`oneStepUniformPerimetralRegimeExit` en fournit l'instance circulaire canonique.

L'interface normative possède un niveau de généralité différent.
`NormativeAdequacy`, `AdequateAlong` et `SpecRelativeHistoryExit` sont
paramétriques sur la norme et le régime, mais leur carrier actuel reste spécialisé
aux `RootedGeneratedHistory P` pour `P : CircularPresentation`.

Dans l'instance `circularNormativeAdequacy`, l'adéquation est globale et constante
sur l'index d'occurrence:

```text
RegimeAdequateAtOccurrence S R H o
  =
(R H → S H) × (S H → R H)
```

`oneStepSpecRelativeHistoryExit` compose la réalisation fidèle, le rejet par le
régime et l'adéquation. La réfutation normative reste démontrée séparément par
`oneStepSpecRelativeHistoryExit_notSpecification`.

La preuve détaillée de ces résultats n'est pas répétée ici; elle se trouve dans
les deux versions du document formel liées en ouverture.

## 7. Généralisation et OOD structurel

Dans ce cadre, généraliser conduit à distinguer:

```text
extension constitutive
transport entre réalisations
maintien ou changement de régime
```

Une extension prolonge une construction. Un transport change son interprétation
concrète tout en préservant les occurrences et accords garantis. Le maintien du
régime demande séparément si la construction conserve son statut d'admission.

Ces opérations ne sont pas équivalentes:

- une construction peut continuer exactement sans conserver son statut;
- une même structure peut changer de réalisation tout en conservant ses
  déterminations garanties;
- une sortie de régime peut être localisée sans supprimer les témoins de fidélité
  déjà établis.

### 7.1 Définition documentaire proposée

La notation suivante introduit une lecture conceptuelle; elle n'est pas une
déclaration Lean du cycle 1:

```text
OOD_struct(P,R,x) :=
  Constructible_P(x)
  ∧ ¬ Admissible_R(x)
```

Elle distingue:

```text
1. constructible et admis
2. constructible mais hors régime
3. non constructible dans la présentation considérée
```

La deuxième situation est l'OOD structurel relatif au régime. Elle ne se confond
ni avec une erreur de construction ni avec une absence de détermination.

L'application circulaire fournit un témoin du schéma correspondant:
`oneStepAfterPerimeter P` existe, est une extension constitutive stricte du
déploiement périmétral et reste exactement interprétable dans toute algèbre
concrète fournie, alors que `CircularRefinement P` est réfuté sur ce candidat.

```text
sortie de régime
  diagnostic structurel

insatisfaction d'une spécification indépendante
+ rejet par un régime adéquat à cette spécification
  diagnostic d'alignement relatif
```

L'OOD structurel et le désalignement relatif ne sont donc pas identifiés. Dans
l'instance circulaire, l'insatisfaction de la norme est prouvée directement et
ne se déduit pas du seul rejet par le régime.

### 7.2 Conséquence interprétative

Dans ce cadre, généraliser ne signifie pas effacer les changements de statut,
mais préserver les déterminations qui subsistent et localiser celles qui cessent
d'être maintenables. Cette formulation est une lecture théorique des constructions
vérifiées, non un théorème universel sur l'OOD des systèmes d'apprentissage.

## 8. La lecture numérique comme conséquence

Une classification n'a pas à précéder toute détermination quantitative.
`positiveContinuation_exactlyOne` fournit directement une détermination
cardinale depuis la structure relationnelle.

```text
structure constituée et conservée
⇒ invariants
⇒ lectures numériques
```

Dans l'application périmétrale, `samePerimeter_length_eq` établit:

```text
CircularRefinement P history
→ history.history.length
  = (perimeterDeployment P).history.length
```

`History.length_append` démontre l'additivité de la longueur pour la
concaténation. L'égalité numérique des longueurs est déduite de la classification
structurelle, et non l'inverse.

La totalité n'est donc pas définie par l'additivité. La loi numérique appartient
à la lecture et à la composition considérées; elle ne détermine pas
rétroactivement le statut du tout.

## 9. Carte des principaux résultats Lean

| Rôle | Déclaration |
|---|---|
| accord exact entre rôle et occurrence | `RequirementOccurrenceAgreement` |
| réalisation locale exacte | `ExactNonClosingRealization` |
| précédence dérivée | `ExactNonClosingRealization.preservesPrecedence` |
| adjacence dérivée | `ExactNonClosingRealization.preservesNext` |
| occurrence résiduelle unique | `positiveExtension_hasUniqueResidualOccurrence` |
| continuation d'une occurrence | `positiveContinuation_exactlyOne` |
| interprétation concrète exacte | `exactlyInterpretHistory` |
| classification exacte d'un régime | `ExactRegimeClassification` |
| sortie typée | `RegimeExit` |
| sortie uniforme | `UniformRegimeExit` |
| norme indépendante | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| carrier completeness | `CircularSpecificationSatisfaction.eq_perimeter` |
| regime completeness | `circularSpecification_complete` |
| adéquation normative | `circularNormativeAdequacy` |
| diagnostic relatif | `oneStepSpecRelativeHistoryExit` |
| égalité de longueur dérivée | `samePerimeter_length_eq` |

## 10. Conclusion stabilisée

Le cycle 1 réalise une chaîne de dépendance précise:

```text
individuation conservée
→ rôles et accords structurels
→ succession et composition
→ histoires et trajectoires
→ invariants
→ lectures numériques
```

Cette architecture permet ensuite de séparer formellement:

```text
construction
réalisation fidèle
admission par un régime
satisfaction d'une norme indépendante
adéquation du régime à cette norme
```

Le résultat n'est pas seulement qu'un candidat est accepté ou rejeté. Il conserve
les témoins de ce qui demeure déterminé et localise exactement la propriété dont
le maintien devient impossible.

> **La contribution structurelle du cycle 1 est une méthode de conservation et
> de diagnostic: préserver les occurrences et leurs relations à travers les
> réalisations, dériver les invariants avant leurs lectures numériques, puis
> distinguer la continuation d'une construction du maintien de son statut
> normatif.**

Le premier cycle mathématique est clos. La suite relève de la documentation, de
la traduction, de l'audit et du versionnement, sans modification des définitions
Lean stabilisées.
