# Reconstruction de l'alignement constitutif

**Francais** | [English](../en/constitutive_alignment_reconstruction.md)

Navigation: [methode](methode_roles_constitutifs_relationnels.md) · [alignement relatif norme/regime](alignement_relatif.md) · [carte architecturale](cartographie_architecturale_verifiee.md)

## Statut

Cette couche formalise une reconstruction constructive de l'alignement entre deux carriers constitutifs initialement distincts.

Elle ne remplace pas l'alignement constitutif deja etabli a partir d'un index commun. Elle ajoute une direction inverse et une couche de decision relative a des donnees relationnelles explicites.

Il faut conserver la separation suivante:

```text
alignement constitutif
=
coherence et reconstruction des identites transportees

adequation normative
=
relation entre un regime et une specification independante
```

Le document [alignement relatif](alignement_relatif.md) traite principalement du second axe. Le present document traite du premier.

La profondeur de genese n'est pas bornee par un entier fixe. Les theoremes de propagation et de reconstruction sont parametres par un `n : Nat` arbitraire. La finitude intervient ailleurs, dans la couche de recherche exhaustive, lorsqu'une enumeration complete des carriers et des ancres est fournie.

---

## 1. Probleme traite

La couche historique d'alignement part d'un carrier constitutif commun et derive les transports entre realisations par l'intermediaire de cet index.

```text
             index commun
             /          \
            v            v
      realisation A  realisation B
```

La nouvelle couche etudie un probleme plus difficile:

```text
Source                     Target
  |                          |
  v                          v
construction A          construction B

        correspondance ?
```

`Source` et `Target` peuvent etre deux types differents. Aucun carrier initial commun d'identites n'est suppose.

La reconstruction se fait par etapes. Le developpement ne pretend pas deduire une correspondance semantique depuis la seule cardinalite ou depuis une bijection arbitraire.

---

## 2. Reconstruction depuis la genese

Pour une profondeur naturelle `n`, considerons un transport exact terminal:

```text
T : IteratedCarrier Source n
      <->
    IteratedCarrier Target n
```

La condition `PreservesGenesis T` exige que chaque identite apparue comme `fresh` a une profondeur de naissance donnee soit envoyee vers l'identite apparue a la meme profondeur sur le cote cible.

Le transport canonique obtenu a partir d'un transport initial est construit par:

```lean
liftToDepth
```

et preserve automatiquement la genese:

```lean
liftToDepth_preservesGenesis
```

La direction inverse est constructive. Un transport terminal exact qui preserve toute la genese peut etre restreint recursivement a sa partie ancienne jusqu'aux carriers initiaux:

```lean
reconstructInitial
```

Le resultat central est la caracterisation:

```text
PreservesGenesis T
        <->
T est le lift canonique
 d'un transport exact Source <-> Target
```

formalisee par:

```lean
preservesGenesis_iff_reconstructible
```

Ainsi, la genese n'introduit pas de degres de liberte d'alignement nouveaux aux profondeurs ulterieures. Un transport terminal compatible avec toute la stratification de naissance est entierement determine par un transport initial.

Cette etape ne determine cependant pas encore quelle identite initiale de `Source` doit correspondre a quelle identite initiale de `Target`.

---

## 3. Localisation exacte de l'ambiguite

La couche de rigidite formalise que l'ambiguite terminale compatible avec la genese est exactement l'ambiguite deja presente a la base.

`InitialForwardRigid Source Target` signifie que tous les transports exacts initiaux possedent la meme application avant, point par point.

`GenesisForwardRigid Source Target n` exprime la meme unicite a la profondeur `n`, parmi les transports exacts qui preservent la genese.

Le developpement prouve, pour toute profondeur naturelle fournie, l'equivalence entre ces deux formes de rigidite.

La consequence conceptuelle est importante:

```text
genese
fixe toutes les couches nouvelles

mais

genese seule
ne brise pas une symetrie deja presente a la base
```

Les regressions donnent un exemple sur `Bool`: deux transports initiaux distincts peuvent etre releves en transports qui preservent tous deux la genese. La correspondance initiale doit donc etre contrainte par une structure supplementaire.

---

## 4. Profils constitutifs separants

La couche suivante introduit des observations structurelles communes sans postuler un carrier commun d'identites.

Un profil a la forme:

```text
Carrier -> Probe -> Value
```

`ProfileSeparates profile` signifie que l'ensemble complet des observations distingue les identites:

```text
memes observations sur toutes les sondes
        ->
meme identite
```

`PreservesProfile` exprime qu'une application conserve ces observations.

Une propriete de separation cote cible suffit alors a rendre toute application preservant le profil pointwise unique.

Cette couche montre aussi qu'un couple de resolvers aller et retour preservant des profils separants n'a pas besoin de stocker ses lois d'inversion comme hypotheses primitives. Les deux round-trips sont derives de la separation, puis assembles en `ExactTypeTransport`.

Le point metodologique est:

```text
observations separantes
+
compatibilite du mapping
        ->
round-trips derives
```

et non:

```text
bijection supposee
        ->
structure declaree compatible
```

---

## 5. Profils derives de relations ancrees

La couche `AnchoredRelationContext` derive les profils depuis des relations locales.

Elle contient:

```text
sourceRelation : Source -> Source -> Value
targetRelation : Target -> Target -> Value

sourceAnchor : Anchor -> Source
targetAnchor : Anchor -> Target
```

ainsi que la separation des identites par les observations depuis la famille d'ancres.

Pour une identite source `s` et une identite cible `t`, la relation:

```lean
context.Matches s t
```

signifie que toutes leurs observations relativement aux ancres correspondantes sont egales.

Les ancres ne sont pas un index complet d'identites. Elles fournissent une famille commune de points de reference relationnels. La correspondance entre toutes les identites reste a reconstruire.

La separation des profils prouve:

```text
une source a au plus une cible compatible

une cible a au plus une source compatible
```

Autrement dit, `Matches` fournit l'unicite mais pas encore l'existence.

---

## 6. Totalite positive et reconstruction du transport exact

`TotalAnchoredMatching context` fournit constructivement les deux obligations d'existence:

```text
pour chaque source
il existe une cible avec Matches

pour chaque cible
il existe une source avec Matches
```

Les temoins sont des sous-types positifs. Les fonctions `forward` et `backward` sont projetees depuis ces temoins.

L'unicite de `Matches` suffit ensuite a deriver:

```text
backward(forward(x)) = x
forward(backward(y)) = y
```

et donc:

```lean
TotalAnchoredMatching.toExactTransport
```

Le mapping exact n'est plus une donnee primitive libre. Il est reconstruit depuis la relation structurelle et sa totalite constructive.

La propagation a toute profondeur naturelle est ensuite canonique:

```lean
TotalAnchoredMatching.finiteTransport
TotalAnchoredMatching.finiteTransport_preservesGenesis
```

Le nom historique `finiteTransport` designe ici le transport a une profondeur indexee par un naturel. Le parametre `depth : Nat` est arbitraire et aucun maximum n'est impose.

---

## 7. Affaiblissement directionnel et strictesse

La totalite dans une seule direction est conservee comme un resultat propre.

`ForwardAnchoredMatching` produit une application injective:

```text
Source -> Target
```

qui preserve les observations ancrees.

`BackwardAnchoredMatching` fournit le resultat symetrique.

Cette structure ne fabrique pas un inverse lorsque celui-ci n'est pas justifie.

Les regressions construisent un contexte ou le matching avant existe et est injectif, mais aucun matching retour compatible n'existe. Par consequent:

```text
totalite avant
        ->
injection structurelle

mais

totalite avant
        -/->
alignement exact bidirectionnel
```

Cette separation evite de confondre inclusion structurelle et equivalence exacte.

---

## 8. Recherche executable sur des enumerations finies

La couche precedente laisse encore la totalite comme une obligation constructive fournie.

`FiniteAnchoredMatchSearch` ferme cette obligation dans un cas executable precis.

Elle suppose:

```text
une liste complete des ancres
une liste complete de Source
une liste complete de Target
une egalite decidable sur Value
```

`FiniteListing A` contient une liste explicite et une preuve que tout element de `A` appartient a cette liste.

La recherche compare les profils ancres par un test booleen:

```lean
matchesOn
```

puis cherche les correspondants:

```lean
findTarget
findSource
```

Les checks globaux sont:

```lean
forwardTotalCheck
backwardTotalCheck
```

Un check avant reussi construit directement un `ForwardAnchoredMatching`. Le check retour construit symetriquement un `BackwardAnchoredMatching`. Si les deux reussissent, le developpement construit un `TotalAnchoredMatching`, puis un transport exact et sa propagation a tout `n : Nat` demande.

La finitude est une hypothese reelle de cette couche de recherche exhaustive. Elle ne borne pas la profondeur de genese des theoremes de propagation.

---

## 9. Completude de la decision et certificats negatifs

La recherche n'est pas seulement sonore.

`FiniteAnchoredMatchDecision` prouve aussi la direction converse: si un matching structurel total existe, le check correspondant doit renvoyer `true` sur des listes completes.

Ainsi:

```text
forwardTotalCheck = false
        ->
aucun ForwardAnchoredMatching compatible
```

et symetriquement pour le retour.

Un echec de recherche devient donc un certificat constructif de non-existence relativement au contexte ancre et aux enumerations completes fournies. Ce n'est pas simplement un echec d'heuristique.

Le module derive egalement la refutation d'un alignement exact compatible lorsqu'une des deux totalites directionnelles echoue.

---

## 10. Classification constructive des quatre regimes

Les deux checks directionnels induisent quatre regimes:

```text
exact
forwardOnly
backwardOnly
noDirectionalMatching
```

`FiniteAlignmentClassification.classify` calcule directement ce regime et conserve les temoins ou refutations correspondants.

### `exact`

Les deux totalites existent. On obtient un `TotalAnchoredMatching`, un `ExactTypeTransport` initial et un transport exact a tout `n : Nat` demande.

### `forwardOnly`

La totalite source vers cible existe, mais la totalite retour echoue. Le resultat contient une injection structurelle avant et une refutation constructive de tout alignement exact compatible.

### `backwardOnly`

Cas symetrique.

### `noDirectionalMatching`

Aucune totalite directionnelle n'existe relativement au contexte considere. Le certificat refute les deux matchings directionnels et l'alignement exact compatible.

Ce dernier statut ne signifie pas que les deux systems sont sans aucune relation imaginable. Il signifie precisement qu'aucun matching total ancre n'existe dans l'interface consideree.

---

## 11. Persistance directionnelle de la genese

La propagation des identites nouvelles ne demande pas une bijection initiale.

Une simple application initiale injective peut etre relevee recursivement par:

```lean
DirectionalGenesisPersistence.liftMap
```

Si l'application initiale est injective, son relevement reste injectif pour tout `depth : Nat`:

```lean
liftMap_injective
```

Il preserve toutes les strates de genese et commute avec les extensions canoniques:

```lean
liftMap_preservesGenesis
liftMap_embedFrom
```

Un `ForwardAnchoredMatching` produit donc un plongement injectif de genese a toute profondeur naturelle, sans fabriquer de transport retour.

La separation des profils rend le matching directionnel initial pointwise unique. Cette canonicite se propage a tous ses relevements:

```lean
forwardMatching_pointwise_unique
finiteForwardEmbedding_pointwise_unique
```

avec les versions symetriques cote retour.

Dans le regime exact, les plongements directionnels coincident point par point avec les deux directions du transport exact reconstruit.

---

## 12. Chaine de reconstruction obtenue

La chaine formelle peut maintenant etre lue ainsi:

```text
relations locales
        ↓
observations depuis des ancres communes
        ↓
profils separants
        ↓
relation Matches
        ↓
unicite des correspondants
        ↓
totalite constructive ou recherche executable
        ↓
classification directionnelle
        ↓
exact / forwardOnly / backwardOnly / noDirectionalMatching
        ↓
transport exact ou injection directionnelle
        ↓
propagation canonique de la genese
        ↓
coherence a toute profondeur n : Nat demandee
```

Cette branche complete la direction historique:

```text
index commun deja donne
        ↓
transports induits
        ↓
naturalite
```

par une reconstruction partielle en sens inverse:

```text
structure relationnelle compatible
        ↓
matching initial reconstruit ou refute
        ↓
transport initial exact lorsqu'il existe
        ↓
transport de genese canonique
```

---

## 13. Ce qui reste ouvert

La nouvelle couche reduit fortement l'hypothese d'un index commun deja disponible, mais elle ne supprime pas toute structure partagee.

Restent fournis:

- le type commun `Anchor`
- les applications `sourceAnchor` et `targetAnchor`
- le type commun `Value`
- les deux relations locales
- les preuves que les profils ancres separent les identites
- pour la recherche executable, des enumerations completes finies et une egalite decidable sur `Value`

Le prochain probleme structurel est donc plus precis qu'avant:

> **Sous quelles conditions les ancres communes, ou une structure d'observation equivalente, peuvent-elles elles-memes etre reconstruites depuis des systemes presentes sans ce mediateur relationnel fourni ?**

Le developpement ne prouve pas non plus:

- que cette interface est minimale parmi toutes les theories possibles d'alignement
- que les roles, readouts, valeurs, statuts, normes ou proprietes semantiques sont automatiquement transportes
- qu'un objet concret a l'etape `omega` est construit
- que la classification vaut pour des carriers non enumerables dans sa couche de decision executable
- qu'il s'agit d'une theorie generale de l'alignement comportemental de systemes d'IA entraines

Ces limites n'affaiblissent pas le resultat exact obtenu. Elles identifient la prochaine frontiere de reconstruction.

---

## 14. Carte de l'API Lean

| Role mathematique | Declaration Lean |
|---|---|
| preservation de toute la genese | `Alignment.GenesisReconstruction.PreservesGenesis` |
| relevement canonique depuis la base | `Alignment.GenesisReconstruction.liftToDepth` |
| reconstruction du transport initial | `Alignment.GenesisReconstruction.reconstructInitial` |
| caracterisation genese / reconstructibilite | `Alignment.GenesisReconstruction.preservesGenesis_iff_reconstructible` |
| rigidite initiale | `Alignment.GenesisReconstruction.InitialForwardRigid` |
| rigidite a profondeur naturelle | `Alignment.GenesisReconstruction.GenesisForwardRigid` |
| separation par profils | `Alignment.GenesisReconstruction.ProfileSeparates` |
| relation ancree commune | `Alignment.GenesisReconstruction.AnchoredRelationContext` |
| matching defini par observations | `AnchoredRelationContext.Matches` |
| totalite bidirectionnelle constructive | `Alignment.GenesisReconstruction.TotalAnchoredMatching` |
| transport exact reconstruit | `TotalAnchoredMatching.toExactTransport` |
| enumeration constructive finie | `FiniteAnchoredMatchSearch.FiniteListing` |
| check total avant | `FiniteAnchoredMatchSearch.forwardTotalCheck` |
| check total retour | `FiniteAnchoredMatchSearch.backwardTotalCheck` |
| decision complete avant | `FiniteAnchoredMatchDecision.forwardTotalCheck_true_iff_nonempty` |
| decision complete retour | `FiniteAnchoredMatchDecision.backwardTotalCheck_true_iff_nonempty` |
| classification des quatre regimes | `FiniteAlignmentClassification.classify` |
| plongement directionnel de genese | `DirectionalGenesisPersistence.FiniteGenesisEmbedding` |
| unicite du matching avant | `DirectionalGenesisPersistence.forwardMatching_pointwise_unique` |
| unicite du relevement avant | `DirectionalGenesisPersistence.finiteForwardEmbedding_pointwise_unique` |

---

## 15. Lecture theorique

Le resultat ne dit pas que deux systemes deviennent alignes parce qu'une bijection existe entre leurs carriers.

Il etablit une chaine plus restrictive:

```text
relations suffisamment discriminantes
+
references ancrees compatibles
        ↓
correspondance structurale definie
        ↓
existence ou non-existence decidable dans le cas enumerable
        ↓
transport exact seulement si les deux directions sont justifiees
        ↓
propagation canonique de la genese
```

L'alignement constitutif acquiert ainsi une couche de **reconstruction de l'alignabilite**. La correspondance n'est plus seulement transportee depuis un index commun deja suppose. Dans le cadre relationnel formalise, elle peut etre reconstruite, classee, propagee ou refutee constructivement.