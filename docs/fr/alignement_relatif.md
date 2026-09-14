# Cycle 1 — Alignement relatif à une spécification indépendante

[English](../en/relative_alignment.md) | **Français**

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[méthode](methode_roles_constitutifs_relationnels.md) ·
[Cycle 2 — alignement réflexif](alignement_reflexif.md)

## Statut

**Cycle 1 mathématiquement clos.**

La phase courante est une phase de stabilisation. Aucune définition mathématique du cycle 1 ne doit être rouverte.

Le résultat de référence distingue, pour une présentation `P`, une histoire `H`
et une interprétation concrète `A`:

```text
F_A(H) := ExactConcreteRealization A H
S(H)   := CircularSpecificationSatisfaction P H
R(H)   := CircularRefinement P H
```

Ces trois prédicats ne sont pas identifiés. Leur relation est démontrée par deux
résultats complémentaires:

```text
R(H) → S(H)
S(H) → R(H)
```

auxquels s'ajoute la classification exacte:

```text
S(H) → H = perimeterDeployment P
```

La contribution centrale est la suivante:

> **Le cycle 1 construit et vérifie en Lean un noyau dépendamment typé pour
> l'alignement relatif. Il sépare construction, réalisation fidèle, régime et
> norme indépendante; démontre l'adéquation exacte entre la norme et le régime
> sur leurs carriers; puis produit une continuation à une occurrence qui, comme
> toute histoire générée enracinée, est exactement réalisable dans toute algèbre
> concrète fournie et localise la rupture normative sans nier la continuation de
> la construction.**

La preuve est complète relativement aux données de `CircularPresentation`.
Aucun principe supplémentaire reliant après coup la norme au régime — appelé ici
« pont externe de fermeture » — n'est ajouté pour obtenir la soundness ou la
complétude.

---

## 1. Objet du cycle 1

Le cycle 1 construit un diagnostic relatif dans lequel quatre niveaux restent formellement distincts:

```text
constitution / réalisation
  ExactNonClosingRealization
  ExactConcreteRealization

norme indépendante
  CircularSpecificationSatisfaction

régime
  CircularRefinement

adéquation norme / régime
  NormativeAdequacy
  AdequateAlong

diagnostic relatif
  SpecRelativeHistoryExit
```

Le point architectural central est que la norme n'est pas définie par le régime.

```text
norme S
  construite et testée indépendamment

CircularRefinement
  évalué ensuite relativement à S
```

Le rejet d'un candidat par le régime ne définit donc pas son insatisfaction normative.

### 1.1 Données internes de la présentation

`CircularPresentation` ne contient ni `CircularRefinement`, ni
`CircularSpecificationSatisfaction`, ni une hypothèse affirmant leur adéquation.
Elle fournit les données géométriques de la construction — nœud initial,
périmètre non vide, jonction finale, extrémités, pôles, différence et provenance —
ainsi que trois opérations relatives à la fermeture:

```lean
closeFromIdentification :
  leftEndpoint = rightEndpoint → TotalLoop

loopContractsInitialDifference :
  TotalLoop →
    leftPole initialNode.difference = rightPole initialNode.difference

rejectInitialContraction :
  Provenance initialNode.difference →
  leftPole initialNode.difference = rightPole initialNode.difference → False
```

Le rejet d'une boucle totale est dérivé par composition:

```text
P.TotalLoop
  ↓ P.loopContractsInitialDifference
contraction des pôles de la différence initiale
  ↓ P.rejectInitialContraction P.initialNode.provenance
False
```

Cette dérivation est encapsulée par `CircularPresentation.rejectTotalLoop`. Elle
est utilisée par la norme pour exclure toute continuation stricte qui prétendrait
réaliser une boucle totale.

Le fichier Lean construit en outre `Example.examplePresentation`, une
`CircularPresentation` finie à quatre nœuds dont les extrémités sont distinguées
par `Bool`. Les données internes de la présentation sont donc explicitement
habitées dans le développement; elles ne constituent pas une interface laissée
sans modèle.

---

## 2. Les quatre séparations à préserver

La documentation du cycle 1 doit conserver explicitement les distinctions suivantes:

```text
réalisation ≠ norme

norme ≠ régime

régime ≠ adéquation du régime

diagnostic du candidat ≠ diagnostic du régime
```

### 2.1 Réalisation ≠ norme

Un candidat peut être exactement constitué et fidèlement interprété tout en ne satisfaisant pas la norme indépendante.

La fidélité de réalisation garantit que la structure demandée est correctement réalisée. Elle ne détermine pas à elle seule le statut normatif du candidat.

### 2.2 Norme ≠ régime

`CircularSpecificationSatisfaction` est construite avant sa comparaison à `CircularRefinement`.

La norme possède son propre modèle positif et son propre contre-exemple
canonique. Son contenu ne provient donc pas d'une simple traduction du régime.

Dans cette instance du Cycle 1, le régime et la norme ont néanmoins la même
extension sur les histoires : chacun est habité exactement en
`perimeterDeployment P`. Cette coextension au niveau du porteur est un résultat
dérivé ; elle n'identifie ni leurs types de témoins, ni leurs définitions, ni
leurs chemins de preuve.

### 2.3 Régime ≠ adéquation du régime

`CircularRefinement` est un régime de données opérationnelles riches.

`NormativeAdequacy` exprime séparément la relation entre ce régime et une spécification indépendante. L'adéquation n'est pas un champ caché du régime.

### 2.4 Diagnostic du candidat ≠ diagnostic du régime

Pour `oneStepAfterPerimeter P`, deux résultats différents sont disponibles:

```text
diagnostic sémantique
  CircularSpecificationSatisfaction P candidate -> False

diagnostic de régime
  CircularRefinement P candidate -> False
```

La première réfutation est démontrée directement depuis la norme indépendante.

La seconde est portée par le `RegimeExit`.

Le premier diagnostic ne dépend pas du second.

---

## 3. La norme indépendante

La norme du cycle 1 possède exactement deux composantes primitives:

```lean
structure CircularSpecificationSatisfaction
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  «local» :
    ExactNonClosingRealization P history

  trajectory :
    CircularClosureMeaning P history
```

Le champ `«local»` utilise l'échappement Lean parce que `local` est un mot réservé.

La norme possède donc exactement deux composantes primitives.

```text
local
  ExactNonClosingRealization

trajectory
  CircularClosureMeaning
```

### 3.1 Composante locale

`ExactNonClosingRealization` affirme la réalisation exacte et injective de toutes les exigences non fermantes dans une vraie `RootedGeneratedHistory`.

Cette composante ne contient pas comme champs primitifs:

```text
ordre
adjacence
participation
contiguïté pertinente
```

Ces propriétés ont été étudiées séparément avant d'être dérivées.

En particulier:

```lean
ExactNonClosingRealization.preservesPrecedence
ExactNonClosingRealization.preservesNext
```

établissent respectivement la conservation de la précédence canonique et de l'adjacence constitutive canonique.

On obtient donc:

\[
\boxed{
\texttt{ExactNonClosingRealization}
+
\texttt{RootedGeneratedHistory}
\Longrightarrow
\text{précédence correcte}
+
\text{adjacence constitutive correcte}
}
\]

Le statut local final est:

```text
ExactNonClosingRealization   primitive locale
ordre                        dérivé
adjacence                    dérivée
participation                portée par History
contiguïté pertinente        dérivée
```

### 3.2 Composante trajectorielle

La signification de fermeture est indépendante du régime:

```lean
abbrev CircularClosureMeaning
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  StrictConstitutivePrefix
      (perimeterDeployment P) history →
    P.TotalLoop
```

Cette composante exprime une obligation sur la trajectoire.

Elle ne fournit pas une réalisation opérationnelle de fermeture.

---

## 4. Les deux cas canoniques

Le cycle 1 est discriminant parce que la même norme possède un cas positif et un cas négatif canoniques.

### 4.1 Cas positif: `perimeterDeployment P`

Le déploiement canonique satisfait la composante locale et la composante trajectorielle.

```text
perimeterDeployment P

ExactNonClosingRealization             ✓
CircularClosureMeaning                 ✓
CircularSpecificationSatisfaction      ✓
CircularRefinement                     ✓
```

La satisfaction de `CircularClosureMeaning` est structurellement vacue sur le
déploiement canonique: un `StrictConstitutivePrefix` de ce déploiement vers
lui-même est impossible. Cette forme n'affaiblit pas le pouvoir discriminant de
la norme. L'obligation devient précisément active dès qu'une continuation
stricte est fournie, comme le montre le cas négatif suivant.

Le résultat positif est construit par:

```lean
perimeterDeployment_specificationSatisfaction
```

Le régime canonique positif est:

```lean
identityCircularRefinement
```

### 4.2 Cas négatif: `oneStepAfterPerimeter P`

Le successeur libre à un pas conserve la structure locale exacte et la fidélité concrète, mais il échoue sur la fermeture trajectorielle.

Le terme « minimal » désigne ici une propriété structurelle précise: le suffixe
de continuation porte exactement une occurrence, établie par
`positiveContinuation_exactlyOne`. Il ne désigne pas l'optimum d'une mesure
numérique ajoutée au cadre.

```text
oneStepAfterPerimeter P

ExactNonClosingRealization             ✓
précédence correcte                    ✓
adjacence correcte                     ✓
ExactConcreteRealization A             ✓

CircularClosureMeaning                 ✗
CircularSpecificationSatisfaction      ✗
CircularRefinement                     ✗

régime adéquat à S                     ✓
SpecRelativeHistoryExit pour A fournie ✓
```

La rupture normative est localisée exactement dans `trajectory`.

```text
local exact       ✓
precedence        ✓ dérivée
next              ✓ dérivée

trajectory        ✗
```

La réfutation trajectorielle est directe:

```text
CircularClosureMeaning
        ↓
oneStepAfterPerimeterStrict
        ↓
P.TotalLoop
        ↓
P.rejectTotalLoop
        ↓
False
```

Le régime n'intervient pas dans cette preuve.

---

## 5. Tableau comparatif central

| Propriété | `perimeterDeployment P` | `oneStepAfterPerimeter P` |
|---|---:|---:|
| `ExactNonClosingRealization` | ✓ | ✓ |
| précédence correcte | ✓ | ✓ |
| adjacence constitutive correcte | ✓ | ✓ |
| réalisation concrète fidèle, pour toute `ConcreteContinuationAlgebra P` fournie | ✓ | ✓ |
| `CircularClosureMeaning` | ✓ | ✗ |
| `CircularSpecificationSatisfaction` | ✓ | ✗ |
| `CircularRefinement` | ✓ | ✗ |
| régime adéquat à `S` | ✓ | ✓ |
| diagnostic relatif négatif, pour une `ConcreteContinuationAlgebra P` fournie | — | ✓ |

La lecture correcte du tableau est:

> `oneStepAfterPerimeter P` n'échoue ni par absence de constitution locale, ni par perte d'ordre, ni par perte d'adjacence, ni par défaut de fidélité concrète. Il échoue sur la composante trajectorielle de la norme indépendante.

---

## 6. Reconstruction structurelle du périmètre

Une étape déterminante du cycle 1 est la reconstruction d'une `PerimeterExtension` depuis la seule réalisation locale exacte:

```lean
ExactNonClosingRealization.toPerimeterExtension
```

Le résultat a la forme:

```text
ExactNonClosingRealization P H
        ↓
copie exacte des occurrences canoniques
        ↓
factorisation initiale de H.history
        ↓
suffixe après perimeterHistory P
        ↓
PerimeterExtension P H
```

Cette reconstruction est structurelle. Elle ne passe pas par une longueur, un rang numérique ou un décompte externe.

Les principaux auxiliaires sont:

```text
embedPerimeterOccurrence
embedPerimeterOccurrence_locatedStep
embedPerimeterOccurrence_injective

History.factorInitialGeneratedStep
History.extractRightOccurrenceAfterSingle

factorDeployRemainingFromExactOccurrences
ExactNonClosingRealization.toPerimeterExtension
```

Cette étape est le verrou constructif qui permet ensuite la carrier completeness.

---

### 6.1 Persistance constitutive exacte à un pas

La continuation canonique porte aussi un résultat indépendant du contenu,
distinct de ses statuts ultérieurs d'admission et de satisfaction normative.
Notons `I0` les occurrences libres du périmètre et `I1` celles de sa
continuation à un pas. `ConstitutivePersistence.freeOccurrenceSplit` construit
un transport exact à deux inverses :

```text
I0 + Unit  <->  I1
```

Chaque occurrence de la continuation est ainsi classée constructivement comme
une occurrence antérieure ou comme l'occurrence nouvelle distinguée. Pour toute
algèbre concrète fournie `A`, l'interprétation exacte donne deux raccords
séparés :

```text
I0 <-> C0[A]
I1 <-> C1[A]
```

Le transport entre deux réalisations est dérivé de ces indices communs ; aucun
raccord concret pair à pair n'est ajouté. Lean démontre la naturalité des
parties ancienne et nouvelle ainsi que la cohérence ponctuelle des chemins :

```text
T1[A,B](old[A](x)) = old[B](T0[A,B](x))
T1[A,B](fresh[A])  = fresh[B]
T[B,C](T[A,B](x))  = T[A,C](x)
```

Un transport candidat sur le porteur étendu est aussi déterminé ponctuellement
dès que son action est fixée sur chaque occurrence antérieure et sur
l'occurrence nouvelle. Il s'agit d'une unicité relative à la décomposition
complète, non de l'unicité de toute correspondance exacte possible.

`ExactOneStepConstitutiveAlignment` extrait exactement le porteur de transition
et sa décomposition ancienne/nouvelle. Sa structure `Realization`, maintenue
séparée, ne contient que les deux porteurs concrets et leurs raccords exacts. Il
s'agit donc d'une réalisation exacte des porteurs, non d'une affirmation portant
à elle seule sur les étiquettes, l'ordre ou la sémantique des pas. Aucune des
deux structures ne mentionne une `CircularPresentation`, une admission, une
spécification ou un readout. La continuation canonique du Cycle 1 instancie
cette abstraction et démontre en outre que les éléments ancien et nouveau
induits sont les occurrences concrètes natives `.earlier` et `.last`.
L'algèbre journalisée non identitaire fournit une réalisation concrète des
porteurs du même alignement. Ces instanciations en établissent la portée ; la
signature indépendante du contenu en porte la généralité. Le développement
actuel démontre la suffisance de cette interface, mais ne revendique pas de
théorème de minimalité stricte pour l'ensemble de ses champs.

### 6.2 Persistance constitutive finie

La décomposition à un pas est itérée sans chaîne ω. `DepthExtension k n` est
un témoin fini positif que la profondeur `n` a été atteinte depuis `k`, et
`IteratedCarrier I n` conserve le porteur initial tout en ajoutant une identité
nouvelle à chaque étape. Les raccords exacts induisent le prolongement vertical
`E` et le changement horizontal de réalisation `T` ; aucun des deux n'est
stocké comme donnée de matching indépendante. Lean démontre ponctuellement :

```text
E[A,l,n](E[A,k,l](x)) = E[A,k,n](x)
T[n,B,C](T[n,A,B](x)) = T[n,A,C](x)
T[n,A,B](E[A,k,n](x)) = E[B,k,n](T[k,A,B](x)).
```

`Cycle1.IteratedConstitutivePersistence` instancie ces lois avec les histoires
réelles construites récursivement par `generate` et `appendGenerated`. À chaque
étape successeur, les occurrences antérieures sont les occurrences natives
`.earlier` et l'identité nouvelle est l'occurrence native `.last`. Le résultat
couvre une identité depuis sa propre profondeur finie de constitution, et non
seulement les identités déjà présentes au périmètre.

Les lectures sont attachées ensuite. Leur type arbitraire de valeurs ne joue
aucun rôle dans le carré commutatif. Sous le prolongement fini de la lecture,
toute distinction déjà établie à la profondeur `k` persiste à chaque profondeur
ultérieure fournie.
L'exemple clos à trois étapes calcule les valeurs périmétrales `7` et `11`, puis
les valeurs nouvelles successives `10`, `20` et `30`, dans les réalisations
libre et journalisée. Cela établit une portée exécutable, non l'instanciation
d'un transformer ni un accord sémantique entre des lectures fournies
indépendamment.

---

## 7. Soundness et completeness

Trois résultats clos établissent l'alignement relatif.

### 7.1 Soundness

```text
CircularRefinement P H
→ CircularSpecificationSatisfaction P H
```

Déclaration Lean:

```lean
circularRefinement_soundSpecification
```

La preuve projette les données riches du régime vers les deux obligations de la norme.

```text
CircularRefinement
        |
        +--> extension
        |      ↓
        |  ExactNonClosingRealization
        |
        +--> strictRefinementProducesTotalLoop
               ↓
          CircularClosureMeaning
```

La soundness signifie:

> tout carrier admis par `CircularRefinement` satisfait la norme indépendante.

### 7.2 Carrier completeness

```text
CircularSpecificationSatisfaction P H
→ H = perimeterDeployment P
```

Déclaration Lean:

```lean
CircularSpecificationSatisfaction.eq_perimeter
```

La preuve utilise:

```text
S.«local»
  ↓
ExactNonClosingRealization.toPerimeterExtension
  ↓
PerimeterExtension

continuation
  ├─ root
  |    ↓
  |  H = perimeterDeployment P
  |
  └─ positive
       ↓
     StrictConstitutivePrefix
       ↓
     S.trajectory
       ↓
     P.TotalLoop
       ↓
     P.rejectTotalLoop
       ↓
     False
```

Ce résultat mérite le nom de **carrier completeness**:

\[
\boxed{
S(P,H)
\Longrightarrow
H = perimeterDeployment(P)
}
\]

### 7.3 Regime completeness

```text
CircularSpecificationSatisfaction P H
→ CircularRefinement P H
```

Déclaration Lean:

```lean
circularSpecification_complete
```

La preuve ne reconstruit aucun champ opérationnel du régime depuis la sémantique de fermeture.

Elle passe par:

```text
S P H
  ↓ eq_perimeter
H = perimeterDeployment P
  ↓ transport
identityCircularRefinement P
  ↓
CircularRefinement P H
```

La regime completeness est donc obtenue par classification du carrier canonique.
La preuve est interne au cadre et n'ajoute, après définition de
`CircularPresentation`, aucun principe supplémentaire reliant la norme au
régime.

---

## 8. Asymétrie entre soundness et regime completeness

Les deux directions comparatives ont des fondements différents:

```text
R -> S
  projection des données riches du régime

S -> R
  classification du carrier
  + transport du témoin canonique
```

Cette asymétrie est essentielle. Elle montre que la conformité du régime à la norme est démontrée par les structures internes du cadre et par la classification du carrier, sans donnée de fermeture ajoutée de l'extérieur.

---

## 9. Adéquation normative

L'architecture possède ici deux niveaux de généralité. `RegimeExit` et
`UniformRegimeExit` sont polymorphes sur un carrier arbitraire et ne présupposent
ni histoire, ni périmètre, ni circularité. L'interface normative présentée
ci-dessous est, quant à elle, paramétrique sur la norme et le régime, mais reste
spécialisée aux `RootedGeneratedHistory P` pour
`P : CircularPresentation`.

Cette interface normative conserve l'indexation par occurrence:

```lean
structure NormativeAdequacy
    (P : CircularPresentation) where
  AlignmentSpec : Type _
  RegimeAdequateAtOccurrence :
    AlignmentSpec →
    (R : RootedGeneratedHistory P → Type _) →
    (H : RootedGeneratedHistory P) →
    History.Occurrence H.history →
    Type _
```

L'instance circulaire du cycle 1 utilise une spécification d'histoire:

```lean
abbrev HistoryAlignmentSpec
    (P : CircularPresentation) :=
  RootedGeneratedHistory P → Type _
```

puis une adéquation globale, constante sur l'index d'occurrence:

```lean
def circularNormativeAdequacy
    (P : CircularPresentation) :
    NormativeAdequacy P where
  AlignmentSpec := HistoryAlignmentSpec P
  RegimeAdequateAtOccurrence :=
    fun S R H _occurrence =>
      (R H → S H) × (S H → R H)
```

Cette instance ne projette pas l'occurrence vers:

```text
source
target
cursor
reading
```

Sur ce même carrier d'histoires, l'interface reste donc compatible avec des
spécifications ultérieures qui dépendraient réellement de l'occurrence. Une
extension à un carrier normatif entièrement arbitraire demanderait une
généralisation supplémentaire de cette interface, sans modifier le noyau
`RegimeExit`.

L'adéquation concrète est:

```lean
circularRefinement_adequateAlong
```

et repose exactement sur:

```text
circularRefinement_soundSpecification
circularSpecification_complete
```

---

## 10. Diagnostic relatif final

Le paquet final est:

```lean
oneStepSpecRelativeHistoryExit
```

Il combine:

```text
candidate
  oneStepAfterPerimeter P

faithful
  ExactConcreteRealization A candidate

inadmissible
  CircularRefinement P candidate -> False

adequacy
  AdequateAlong ... candidate
```

La structure générique `SpecRelativeHistoryExit` n'est pas modifiée pour y ajouter une réfutation de la norme.

La réfutation sémantique reste séparée:

```lean
oneStepSpecRelativeHistoryExit_notSpecification
```

Elle passe directement par:

```lean
oneStepAfterPerimeter_notSpecificationSatisfaction
```

et non par `exit.inadmissible`.

Le diagnostic final possède donc trois couches distinctes:

```text
constitution / réalisation
  candidat généré enraciné
  réalisation exacte disponible uniformément pour toute histoire de ce type

norme
  candidat ne satisfait pas S

régime
  candidat est rejeté
  et le régime est adéquat à S
```

La formulation synthétique est:

\[
\boxed{
\text{réalisation fidèle}
+
\text{insatisfaction de }S
+
\text{rejet par un régime adéquat à }S
}
\]

---

## 11. Ce que signifie ici "alignement relatif"

Le cycle 1 ne formalise pas une théorie générale de l'alignement.

Il établit, dans le cadre considéré, un diagnostic relatif à une spécification explicite et indépendante.

Le cas positif est:

```text
perimeterDeployment P

S                                ✓
CircularRefinement               ✓
```

Le cas négatif est:

```text
oneStepAfterPerimeter P

réalisation fidèle               ✓
S                                ✗
CircularRefinement               ✗
régime adéquat à S               ✓
```

La formulation correcte est donc:

> le candidat `oneStepAfterPerimeter P` est insatisfaisant relativement à `S`, tandis que le régime `CircularRefinement` est adéquat à cette norme et rejette correctement ce candidat.

Il ne faut pas dire que `oneStepAfterPerimeter P` est un régime.

Il ne faut pas non plus dire que le régime est désaligné avec `S` dans ce cas.

---

## 12. Carte de l'API Lean

| Rôle mathématique | Déclaration Lean |
|---|---|
| réalisation locale exacte | `ExactNonClosingRealization` |
| précédence dérivée | `ExactNonClosingRealization.preservesPrecedence` |
| adjacence dérivée | `ExactNonClosingRealization.preservesNext` |
| reconstruction du préfixe périmétral | `ExactNonClosingRealization.toPerimeterExtension` |
| décomposition exacte à un pas | `ConstitutivePersistence.freeOccurrenceSplit` |
| alignement abstrait à un pas | `ExactOneStepConstitutiveAlignment` |
| réalisation exacte d'un alignement | `ExactOneStepConstitutiveAlignment.Realization` |
| alignement abstrait canonique | `ConstitutivePersistence.canonicalOneStepAlignment` |
| accord avec l'occurrence ancienne native | `ConstitutivePersistence.concreteOldEmbedding_isEarlier` |
| accord avec l'occurrence nouvelle native | `ConstitutivePersistence.concreteNewOccurrence_isLast` |
| cohérence concrète des chemins | `ConstitutivePersistence.extendedConcreteTransport_forward_comp` |
| norme trajectorielle | `CircularClosureMeaning` |
| norme indépendante | `CircularSpecificationSatisfaction` |
| modèle positif de la norme | `perimeterDeployment_specificationSatisfaction` |
| contre-exemple canonique | `oneStepAfterPerimeter_notSpecificationSatisfaction` |
| carrier completeness | `CircularSpecificationSatisfaction.eq_perimeter` |
| regime completeness | `circularSpecification_complete` |
| soundness | `circularRefinement_soundSpecification` |
| spécification d'histoire | `HistoryAlignmentSpec` |
| instance d'adéquation | `circularNormativeAdequacy` |
| adéquation le long d'une histoire | `circularRefinement_adequateAlong` |
| diagnostic relatif | `oneStepSpecRelativeHistoryExit` |
| réfutation sémantique depuis le paquet | `oneStepSpecRelativeHistoryExit_notSpecification` |

---

## 13. Réflexion propositionnelle dans le Cycle 2

Les déclarations du Cycle 1 ci-dessus sont des applications entre types de
témoins porteurs d'information de preuve :

```text
CircularRefinement P H
  → CircularSpecificationSatisfaction P H

CircularSpecificationSatisfaction P H
  → CircularRefinement P H
```

Le Cycle 2 observe explicitement leur habitabilité :

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

`Cycle2.ReflectiveAlignment.circularStatusAdequacy` démontre alors la véritable
équivalence propositionnelle :

```text
CircularRegimeStatus P H
  ↔ CircularSpecificationStatus P H
```

Ce raccord est implémenté et constructif. Il est dérivé des deux applications du
Cycle 1 ; il ne modifie pas le Cycle 1 et ne revendique ni `Equiv` ni égalité
entre les structures de témoins originelles. C'est le point formel depuis lequel
le Cycle 2 transporte l'adéquation établie dans la couche de représentation.

---

## 14. Audit et reproductibilité

Depuis la racine du dépôt, reproduire la compilation épinglée avec :

```bash
lake clean
lake build
```

Puis vérifier le manifeste des sources scientifiques avec :

```bash
bash scripts/verify-manifest.sh
```

ou :

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

L'environnement complet, les empreintes des sources, les décomptes de
compilation et le résultat de l'audit axiomatique sont consignés dans
[`audit/AUDIT_BUILD.txt`](../../audit/AUDIT_BUILD.txt). Aucun dépôt antérieur ni
historique source privé n'est requis.

Les déclarations finales du raccord d'alignement sont également auditées:

```text
HistoryAlignmentSpec
circularNormativeAdequacy
circularRefinement_adequateAlong
oneStepSpecRelativeHistoryExit
oneStepSpecRelativeHistoryExit_notSpecification
```

La compilation confirme que Lean accepte les artefacts courants sans
avertissement. Toutes les commandes `#print axioms` des blocs finaux rapportent
que les déclarations inspectées ne dépendent d'aucun axiome.

Les récursions dépendantes qui produisent des témoins dans la chaîne locale vers
globale sont écrites sous une forme structurelle exécutable, et le compilateur
émet une représentation intermédiaire (IR) pour chacune. Sur des présentations et
réalisations closes, la reconstruction se réduit à des valeurs concrètes. Les
sources Lean ne contiennent aucune déclaration `noncomputable` ; ce contrôle
textuel reste distinct des tests de génération de code comme de l'audit
axiomatique.

---

## 15. Conclusion stabilisée

Le cycle 1 établit trois résultats de fermeture:

```text
soundness
  CircularRefinement P H
  → CircularSpecificationSatisfaction P H

carrier completeness
  CircularSpecificationSatisfaction P H
  → H = perimeterDeployment P

regime completeness
  CircularSpecificationSatisfaction P H
  → CircularRefinement P H
```

Il fournit en outre un diagnostic concret sur
`h⁺ := oneStepAfterPerimeter P`:

```text
ExactConcreteRealization A h⁺             habité pour toute A fournie
CircularSpecificationSatisfaction P h⁺    réfuté directement
CircularRefinement P h⁺                   réfuté par le régime
adéquation du régime à la norme            démontrée
```

La réalisation concrète exacte n'est pas propre à `h⁺` : la même construction
interprète toute histoire générée enracinée. Les deux réfutations sont relatives
à la `CircularPresentation` fournie, en particulier à son champ explicite
`rejectInitialContraction`.

La preuve d'alignement est complète relativement à la présentation et à la norme
du cycle 1. Elle n'identifie pas réalisation, satisfaction et admission; elle
démontre séparément leur relation et localise exactement leur séparation sur le
candidat libre à un pas.

### Invariants de stabilisation

Les modifications documentaires et de versionnement doivent préserver:

```text
les définitions et signatures mathématiques
la norme CircularSpecificationSatisfaction
le régime CircularRefinement
le contraste entre les deux cas canoniques
l'absence de pont ajouté entre norme et régime
les résultats d'audit axiomatique
```

Le raccord propositionnel de la section 13 appartient au Cycle 2. Il observe le
résultat clos du Cycle 1 sans modifier ses types de témoins ni son contenu
mathématique.

### Énoncé de publication

> **Le cycle 1 construit et vérifie en Lean un noyau dépendamment typé pour
> l'alignement relatif. Il sépare construction, réalisation fidèle, régime et
> norme indépendante; démontre la soundness et la complétude de leur accord sur
> les histoires admises; puis construit une continuation à une occurrence qui,
> comme toute histoire générée enracinée, demeure exactement réalisable sous
> toute implémentation concrète conforme à l'interface, tout en étant rejetée par
> la norme et par un régime démontré adéquat à cette norme. Ces réfutations sont
> relatives à l'obstruction explicite de fermeture fournie par
> `CircularPresentation`.**

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d'OpenAI, sous direction humaine et au cours
> d'interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
