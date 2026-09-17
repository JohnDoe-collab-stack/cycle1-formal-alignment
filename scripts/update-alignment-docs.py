from pathlib import Path
import hashlib


def read(path):
    return Path(path).read_text(encoding='utf-8')


def write(path, text):
    Path(path).write_text(text, encoding='utf-8')


def replace_once(path, old, new):
    text = read(path)
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{path}: expected exactly one occurrence, found {count}: {old[:100]!r}')
    write(path, text.replace(old, new, 1))


def replace_from(path, marker, new_tail):
    text = read(path)
    index = text.find(marker)
    if index < 0:
        raise SystemExit(f'{path}: missing marker {marker!r}')
    if text.find(marker, index + 1) >= 0:
        raise SystemExit(f'{path}: marker occurs more than once {marker!r}')
    write(path, text[:index] + new_tail.rstrip() + '\n')


def insert_before(path, marker, block):
    text = read(path)
    index = text.find(marker)
    if index < 0:
        raise SystemExit(f'{path}: missing insertion marker {marker!r}')
    if text.find(marker, index + 1) >= 0:
        raise SystemExit(f'{path}: insertion marker occurs more than once {marker!r}')
    write(path, text[:index] + block.rstrip() + '\n\n' + text[index:])


# Fix one typo in the new French guide.
replace_once(
    'docs/fr/reconstruction_alignement_constitutif.md',
    'les deux systems sont sans aucune relation imaginable',
    'les deux systemes sont sans aucune relation imaginable')

# French long presentation: update the old common-index limitation, then replace the old open-problem tail.
replace_once(
    'PRESENTATION_LONGUE.md',
    "Dans l’état actuel de la théorie, cet index commun est fourni ou extrait d’une construction commune. La théorie ne prétend pas encore reconstruire automatiquement un tel médiateur entre deux systèmes initialement présentés comme indépendants.",
    "Cette architecture reste la description correcte du transport entre plusieurs réalisations d'une détermination déjà indexée. La branche de reconstruction ajoute désormais une direction inverse pour deux carriers initiaux distincts : elle ne suppose pas un carrier initial commun d'identités, mais reconstruit une correspondance compatible à partir de la genèse et de profils relationnels ancrés. Elle ne reconstruit toutefois pas encore la famille d'ancres elle-même depuis deux systèmes dépourvus de tout médiateur relationnel fourni.")

fr_tail = r'''### 8.11 Reconstruction du transport depuis la genèse

La branche de reconstruction étudie maintenant deux carriers initiaux distincts :

```text
Source
Target
```

Aucun carrier initial commun d'identités n'est supposé.

A une profondeur naturelle arbitraire `n`, on peut considérer un transport exact terminal :

```text
T : IteratedCarrier Source n
      <->
    IteratedCarrier Target n
```

La propriété `PreservesGenesis T` exige que chaque identité fraîche soit transportée vers l'identité née à la même profondeur du côté cible.

Le développement prouve alors deux directions.

Un transport exact initial se relève canoniquement par `liftToDepth`, et ce relevement préserve toute la genèse.

Inversement, un transport terminal exact qui préserve toute la genèse peut être restreint récursivement à sa partie ancienne jusqu'aux carriers initiaux par `reconstructInitial`.

La caractérisation centrale est :

```text
PreservesGenesis T
        <->
T est le relevement canonique
 d'un transport exact Source <-> Target
```

formalisée par :

```lean
preservesGenesis_iff_reconstructible
```

La genèse ne rajoute donc pas de degrés de liberté d'alignement aux profondeurs ultérieures. Toute ambiguïté compatible avec la genèse provient de la correspondance initiale.

### 8.12 Rigidité et localisation de l'ambiguïté

Cette dernière affirmation est elle-même formalisée.

`InitialForwardRigid Source Target` exprime l'unicité ponctuelle de l'application avant parmi les transports exacts initiaux.

`GenesisForwardRigid Source Target n` exprime l'unicité correspondante parmi les transports exacts de profondeur `n` qui préservent la genèse.

La rigidité initiale et la rigidité à profondeur naturelle sont équivalentes.

```text
genèse
        ->
fixe les couches nouvelles

mais

genèse seule
        -/->
brise une symétrie initiale
```

Les séparateurs sur `Bool` montrent effectivement que deux transports initiaux distincts peuvent être relevés tout en préservant tous les deux la genèse.

La question se déplace donc vers la structure capable d'individuer les identités initiales.

### 8.13 Profils constitutifs et relations ancrées

La couche suivante introduit des observations structurelles sans réintroduire un index commun d'identités.

Un profil :

```text
Carrier -> Probe -> Value
```

est séparant lorsque l'égalité de toutes ses observations force l'égalité des identités.

Cette propriété est formalisée par `ProfileSeparates`.

Deux fonctions qui préservent un même profil séparant sont alors ponctuellement déterminées.

Le développement dérive ensuite ces profils depuis des relations locales à une famille d'ancres correspondantes :

```text
sourceRelation : Source -> Source -> Value
targetRelation : Target -> Target -> Value

sourceAnchor : Anchor -> Source
targetAnchor : Anchor -> Target
```

`AnchoredRelationContext.Matches s t` signifie que `s` et `t` possèdent les mêmes observations relativement à toutes les ancres correspondantes.

Les ancres ne codent pas la correspondance complète. Elles servent de références relationnelles communes.

La séparation prouve seulement l'unicité :

```text
une source a au plus une cible compatible
une cible a au plus une source compatible
```

L'existence reste une obligation distincte.

Lorsque cette existence est donnée constructivement dans les deux directions par `TotalAnchoredMatching`, les applications `forward` et `backward` sont projetées des témoins positifs et leurs round-trips sont dérivés de l'unicité de `Matches`.

On reconstruit alors :

```lean
TotalAnchoredMatching.toExactTransport
```

puis son relevement canonique à tout `n : Nat` demandé.

Le transport exact initial n'est donc plus, dans cette couche, un choix libre posé avant la structure relationnelle.

### 8.14 Recherche executable et classification de l'alignabilité

La totalité peut elle-même être fermée constructivement dans le cas enumerable.

`FiniteAnchoredMatchSearch` suppose des listes finies complètes des ancres, de `Source` et de `Target`, ainsi qu'une égalité décidable sur les valeurs d'observation.

Il calcule :

```text
forwardTotalCheck
backwardTotalCheck
```

Un check avant réussi construit un `ForwardAnchoredMatching`.

Un check retour réussi construit un `BackwardAnchoredMatching`.

Les deux checks réussis construisent un `TotalAnchoredMatching`, puis un transport exact.

La couche de décision prouve aussi la réciproque : si le matching correspondant existe, le check doit réussir sur les listes complètes. Un résultat `false` devient ainsi un certificat constructif de non-existence relativement au contexte ancré fourni.

Les deux directions produisent une classification executable en quatre régimes :

```text
exact
forwardOnly
backwardOnly
noDirectionalMatching
```

Le cas `exact` fournit un transport exact.

Le cas `forwardOnly` fournit une injection structurelle source vers cible et réfute un alignement exact compatible.

Le cas `backwardOnly` est symétrique.

Le cas `noDirectionalMatching` réfute les deux totalités directionnelles relativement au contexte considéré.

Cette classification ne doit pas être surinterprétée. `noDirectionalMatching` ne signifie pas que les deux systèmes sont absolument sans relation. Il signifie qu'aucun matching total défini par les observations ancrées choisies n'existe.

La finitude est ici une hypothèse réelle de la recherche exhaustive. Elle ne borne pas la profondeur de genèse, qui reste paramétrée par un `n : Nat` arbitraire.

### 8.15 Persistance directionnelle

L'alignement exact n'est pas nécessaire pour propager une inclusion structurelle justifiée.

Un matching avant fournit une application injective initiale. Cette application est relevée récursivement à tout `depth : Nat` en conservant les anciennes identités et en envoyant chaque nouvelle identité vers le `fresh` de même profondeur.

Le relevement :

```text
reste injectif
préserve toutes les strates de genèse
commute avec les extensions canoniques
```

sans fabriquer d'inverse.

Le cas `backwardOnly` possède la construction symétrique.

La séparation des profils rend en outre le matching directionnel ponctuellement unique, et cette canonicité se propage à tout relevement naturel.

Dans le cas `exact`, les deux plongements directionnels coïncident point par point avec les directions avant et arrière du transport exact reconstruit.

Ainsi, la classification n'est pas seulement statique. Chaque régime transporte exactement la structure dynamique qu'il justifie.

### 8.16 De l'alignement donné à l'alignabilité reconstruite

La théorie possède maintenant deux mouvements complémentaires.

Le premier est le mouvement historique :

```text
index constitutif commun déjà donné
        ↓
réalisations exactes
        ↓
transports induits
        ↓
composition et naturalité
```

Le second est une reconstruction partielle en sens inverse :

```text
relations locales
        ↓
profils ancrés séparants
        ↓
Matches
        ↓
matching initial reconstruit, directionnel ou réfuté
        ↓
transport exact lorsque les deux directions sont justifiées
        ↓
relevement canonique de la genèse
```

L'alignement constitutif ne se limite donc plus au suivi cohérent d'une identité à partir d'un index commun déjà disponible.

Dans le cadre relationnel formalisé, le développement commence aussi à caractériser **l'alignabilité elle-même** : il peut reconstruire, classifier ou réfuter la correspondance compatible relativement à une famille d'observations ancrées.

Cette extension ne modifie pas l'ordre de dépendance fondamental. L'identité n'est toujours pas fabriquée par le matching. Les profils ancrés doivent distinguer des identités déjà constituées dans chacun des deux systèmes.

### 8.17 Frontière actuelle de la reconstruction

La nouvelle couche réduit fortement l'hypothèse d'un index commun déjà disponible, mais elle ne supprime pas toute structure partagée.

Restent fournis :

```text
le type Anchor
les applications sourceAnchor et targetAnchor
le type Value
les deux relations locales
la séparation des profils ancrés
```

Et, pour la couche de décision executable :

```text
des listes finies complètes
de Source, Target et Anchor
+
une égalité décidable sur Value
```

La prochaine frontière théorique devient donc :

> **Sous quelles conditions la famille d'ancres communes, ou une structure d'observation équivalente, peut-elle elle-même être reconstruite depuis deux systèmes présentés sans ce médiateur relationnel fourni ?**

La théorie actuelle ne démontre pas non plus que son interface soit minimale parmi toutes les formalisations possibles.

Elle ne transporte pas automatiquement les rôles, lectures, valeurs, statuts, normes ou propriétés sémantiques attachés aux identités.

Elle est uniforme pour tout `n : Nat` et n'impose aucune profondeur maximale. Elle ne construit pas pour autant un carrier concret à l'étape `omega`.

Enfin, cette couche ne constitue pas par elle-même une théorie de l'alignement comportemental ou normatif de systèmes d'intelligence artificielle entraînés.

### 8.18 Chaîne théorique complète

La chaîne complète peut désormais être formulée ainsi :

```text
relations constitutives
        ↓
individuation
        ↓
rôles constitutifs relationnels
        ↓
analyse des dépendances
        ↓
séparation et reconstruction
        ↓
instance circulaire
        ↓
reconstruction du tout constitutif
        ↓
continuation
        ↓
résiduel unique
        ↓
frontière constitutive du régime
        ↓
identité fraîche
        ↓
indexation et provenance structurelle
        ↓
persistance pour tout n : Nat
        ↓
transports induits entre réalisations
        ↓
composition, naturalité et cohérence médiée
        ↓
alignement constitutif
        ↓
reconstruction par genèse entre carriers distincts
        ↓
profils relationnels ancrés
        ↓
reconstruction ou réfutation du matching initial
        ↓
classification de l'alignabilité
        ↓
persistance exacte ou directionnelle selon le régime
```

Le mouvement théorique possède donc maintenant deux sens.

Depuis la constitution, il détermine une identité puis établit comment elle persiste et se transporte.

Depuis deux carriers déjà constitués, il peut aussi remonter depuis la compatibilité de genèse et la structure relationnelle vers la correspondance initiale qui rend leur transport légitime.

La frontière ouverte n'est plus simplement l'absence d'un index commun. Elle est la reconstruction du médiateur relationnel qui permet de définir les observations ancrées elles-mêmes.
'''
replace_from('PRESENTATION_LONGUE.md', '### 8.11 Ce que', fr_tail)

# English long presentation: replace the old compact alignment section with the current architecture.
en_alignment = r'''## 8. Constitutive alignment

Alignment is not the starting point of the theory. It is a coherence layer obtained after constitution, identity genesis, indexing, and persistence.

The question is not whether two realizations look similar. It is whether the legitimate transformations between realizations and depths track the same already constituted identities coherently.

### 8.1 Constitutive alignment and normative adequacy

Two relations must remain distinct:

```text
constitutive alignment
=
coherence and reconstruction of transported identities

normative adequacy
=
relation between a regime and an independent specification
```

Neither relation defines the other.

### 8.2 Dependency order of alignment

The forward alignment architecture has the order:

```text
already constituted identities
        ↓
shared constitutive indexing
        ↓
exact realizations of that index
        ↓
induced horizontal transports
        +
induced vertical extensions
        ↓
composition
        ↓
naturality
        ↓
constitutive alignment
```

An exact carrier correspondence is not yet alignment, and similarity of readouts cannot replace constitutive indexing.

### 8.3 Shared index as constitutive mediator

Two realizations of one constituted system are connected to a common canonical carrier:

```text
              shared constitutive index
                /                \
               v                  v
        realization A      realization B
```

Transport between realizations is induced through this common index rather than stored as independent pairwise matching.

For every `n : Nat`, `IteratedCarrier Initial n` retains initial identities and the genesis depth of every fresh identity.

This remains the correct architecture for changing realization once a determination is already indexed. The reconstruction branch now adds a reverse direction for two distinct initial carriers. It assumes no common initial identity carrier, but reconstructs compatible correspondence from genesis and anchored relational profiles. It does not yet reconstruct the anchor family itself from two systems supplied without any common relational mediator.

### 8.4 Old / fresh decomposition and relative uniqueness

At one step, every extended identity is constructively old or fresh. A candidate extended transport that agrees on every old identity and maps fresh to fresh is pointwise forced on the complete extended carrier.

This is relative uniqueness under the constitutive split, not absolute uniqueness of every exact bijection.

### 8.5 Horizontal and vertical composition

Changes of realization compose:

```text
A -> B -> C
=
A -> C
```

Extensions compose:

```text
depth n -> depth m -> depth p
=
depth n -> depth p
```

Extension images are also independent of the particular proof-relevant `DepthExtension` witness chosen between fixed source and target depths.

### 8.6 Naturality

The two axes commute:

```text
extend then change realization
=
change realization then extend
```

This expresses bidimensional coherence of persistence. It does not identify the realizations. It states that legitimate paths for tracking the same constituted identity agree.

### 8.7 Exactness alone is insufficient

The development constructs exact bijections with perfect round trips that permute fresh identities and break the extension / transport square.

Therefore:

```text
exact transport
-/->
constitutive naturality
```

and an arbitrary exact bijection is not constitutive alignment.

### 8.8 Mediated coherence

Concrete paths can first be shown to realize the same transition in a common mediator. This yields observed commutation without global faithfulness.

A local reflection property at the terminal observation is sufficient to lift observed equality to literal equality. Global terminal injectivity is a stronger sufficient condition.

Adjacent mediated squares paste at the observed level without requiring a faithful intermediate boundary. Reflection at the outer terminal is sufficient to recover literal commutation of the pasted rectangle.

### 8.9 Alignment of constituted novelty

In the circular instance:

```text
unique residual occurrence
=
fresh constitutive identity
```

Two exact realizations of the continuation therefore do not independently create two novelties that are later matched by similarity. They co-realize the same new occurrence already determined in the constitutive carrier.

That identity persists to arbitrary later natural depths and its persistence is natural under change of realization.

### 8.10 Theoretical definition

Within the present architecture, a constitutive alignment is the coherence of identity transports induced by constitutive indexing, under change of realization and extension, such that already constituted identities and identities newly determined by the construction remain tracked without confusion and the relevant transport paths compose and commute.

This is an architectural reading of explicit Lean structures and equations, not a replacement primitive predicate.

### 8.11 Reconstruction from genesis

The reconstruction branch considers distinct initial carriers `Source` and `Target` without assuming a common initial identity carrier.

At an arbitrary natural depth `n`, let:

```text
T : IteratedCarrier Source n
      <->
    IteratedCarrier Target n
```

be an exact terminal transport.

`PreservesGenesis T` requires every fresh identity to be transported to the identity born at the same depth on the target side.

An initial exact transport lifts canonically through `liftToDepth`, and the lift preserves genesis. Conversely, a terminal exact transport preserving all genesis strata can be recursively restricted to its old component until the initial carriers are reached by `reconstructInitial`.

The central characterization is:

```text
PreservesGenesis T
        <->
T is the canonical lift
 of an exact transport Source <-> Target
```

formalized by `preservesGenesis_iff_reconstructible`.

Genesis therefore introduces no new alignment freedom at later depths. Every remaining ambiguity comes from the initial correspondence.

### 8.12 Rigidity of the remaining ambiguity

`InitialForwardRigid Source Target` expresses pointwise uniqueness of the forward map among exact initial transports.

`GenesisForwardRigid Source Target n` expresses the corresponding uniqueness among exact genesis-preserving transports at depth `n`.

These forms of rigidity are equivalent for every supplied natural depth.

Genesis fixes generated strata, but it cannot break a symmetry already present at the initial layer. Regression models on `Bool` exhibit this separation constructively.

### 8.13 Separating profiles and anchored relations

The next layer constrains initial correspondence by structural observations without reintroducing a common identity carrier.

A profile `Carrier -> Probe -> Value` is separating when equality of all observations forces identity equality. `ProfileSeparates` formalizes this property.

The development then derives profiles from two local relations observed relative to corresponding anchors:

```text
sourceRelation : Source -> Source -> Value
targetRelation : Target -> Target -> Value

sourceAnchor : Anchor -> Source
targetAnchor : Anchor -> Target
```

`AnchoredRelationContext.Matches s t` states that all anchored observations of `s` and `t` agree.

Anchors are not a complete common identity index. They provide shared relational reference points.

Profile separation gives uniqueness of any counterpart satisfying `Matches`. When positive matching witnesses exist in both directions, `TotalAnchoredMatching` projects the forward and backward maps, derives their round trips from uniqueness, and constructs `ExactTypeTransport`.

### 8.14 Executable search and classification of alignability

In the enumerable case, the totality obligation is itself closed constructively.

`FiniteAnchoredMatchSearch` takes complete finite listings of anchors, `Source`, and `Target`, together with decidable equality on observation values.

It computes:

```text
forwardTotalCheck
backwardTotalCheck
```

A successful one-sided check constructs the corresponding directional matching. Two successful checks construct total matching and exact transport.

The decision layer proves completeness as well as soundness. If a compatible directional matching exists, the corresponding check must return `true`. A `false` result therefore gives a constructive non-existence certificate relative to the supplied anchored context and complete listings.

The two checks produce an executable four-way classification:

```text
exact
forwardOnly
backwardOnly
noDirectionalMatching
```

`forwardOnly` and `backwardOnly` retain the justified structural injection while constructively refuting compatible exact alignment. `noDirectionalMatching` means that neither total anchored matching exists in the chosen interface. It does not claim that the systems are unrelated in every possible sense.

Finiteness is a genuine hypothesis of this exhaustive search layer. It does not bound genesis depth, which remains arbitrary in `Nat`.

### 8.15 Directional persistence

Exact alignment is not required to propagate a justified structural inclusion.

A one-sided injective initial matching lifts recursively to every `depth : Nat`, preserves all fresh-generation strata, and commutes with canonical extensions without manufacturing an inverse.

Profile separation also makes the one-sided matching pointwise unique. This canonicity propagates to all natural-depth lifts.

In the exact regime, the directional lifts agree pointwise with the forward and backward maps of the reconstructed exact transport.

### 8.16 From given alignment to reconstructed alignability

The theory now has two complementary movements.

Forward:

```text
shared constitutive index already given
        ↓
exact realizations
        ↓
induced transports
        ↓
composition and naturality
```

Partial reverse reconstruction:

```text
local relations
        ↓
separating anchored profiles
        ↓
Matches
        ↓
initial matching reconstructed, directional, or refuted
        ↓
exact transport when both directions are justified
        ↓
canonical genesis lift
```

Constitutive alignment therefore now includes a formal layer of **reconstruction of alignability** relative to explicit relational observations.

This does not invert the constitutive dependency order. Anchored profiles must distinguish identities already constituted within each system. Matching still does not manufacture identity.

### 8.17 Current reconstruction boundary

The new layer substantially weakens the assumption that a shared identity index is already available, but it does not remove every shared structure.

The following remain supplied:

```text
the Anchor type
sourceAnchor and targetAnchor
the Value type
the two local relations
separation of anchored profiles
```

Executable decision additionally requires complete finite listings and decidable equality on `Value`.

The next structural problem is therefore:

> **Under what conditions can the shared anchor family, or an equivalent observation structure, itself be reconstructed from two systems presented without that relational mediator?**

The theory does not claim that its interface is globally minimal. It does not automatically transport roles, readouts, values, statuses, norms, or semantic properties. It is uniform for every `n : Nat` and imposes no maximum depth, but it does not construct a concrete carrier at an `omega` stage. It is not by itself a theory of behavioral or normative alignment for trained AI systems.

### 8.18 Complete theoretical chain

```text
constitutive relations
        ↓
individuation
        ↓
relational constitutive roles
        ↓
dependency analysis
        ↓
separation and reconstruction
        ↓
circular instance
        ↓
reconstruction of the constitutive whole
        ↓
continuation
        ↓
unique residual
        ↓
constitutive regime boundary
        ↓
fresh identity
        ↓
indexing and structural provenance
        ↓
persistence for every n : Nat
        ↓
induced transports between realizations
        ↓
composition, naturality, and mediated coherence
        ↓
constitutive alignment
        ↓
genesis reconstruction between distinct carriers
        ↓
anchored relational profiles
        ↓
reconstruction or refutation of initial matching
        ↓
classification of alignability
        ↓
exact or directional persistence according to the regime
```

The theoretical movement now has two directions. Constitution determines an identity and then establishes how it persists and transports. Given two already constituted carriers, the theory can also move from genesis compatibility and relational structure back toward the initial correspondence that makes transport legitimate.

The open boundary is no longer merely the absence of a shared identity index. It is the reconstruction of the relational mediator from which the anchored observations themselves can be defined.
'''
replace_from('LONG_PRESENTATION.md', '## 8. Alignment', en_alignment)

# Dedicated relative-alignment docs: link the new constitutive reconstruction without collapsing it into normative adequacy.
fr_relative_block = r'''### 6.3 Reconstruction de l'alignement constitutif entre carriers distincts

La persistance ci-dessus part d'un index constitutif commun. Une branche formelle distincte étudie désormais le problème inverse entre deux carriers initiaux différents.

Elle reconstruit un transport initial depuis un transport terminal qui préserve toute la genèse, puis contraint la correspondance initiale par des profils relationnels ancrés. Dans le cas enumerable, elle recherche les correspondants, décide les totalités directionnelles et classe le contexte en quatre régimes : `exact`, `forwardOnly`, `backwardOnly` ou `noDirectionalMatching`.

Cette reconstruction reste distincte de l'adéquation norme/régime étudiée dans le présent document.

Voir [Reconstruction de l'alignement constitutif](reconstruction_alignement_constitutif.md) pour le développement complet et les limites exactes.'''
insert_before('docs/fr/alignement_relatif.md', '\n---\n\n## 7. Soundness', fr_relative_block)

en_relative_block = r'''### 6.3 Reconstruction of constitutive alignment between distinct carriers

The persistence layer above starts from a shared constitutive index. A separate formal branch now studies the reverse problem between two different initial carriers.

It reconstructs an initial transport from a terminal transport preserving the whole genesis stratification, then constrains the initial correspondence through anchored relational profiles. In the enumerable case it searches for counterparts, decides directional totality, and classifies the context into four regimes: `exact`, `forwardOnly`, `backwardOnly`, or `noDirectionalMatching`.

This reconstruction remains distinct from the norm/regime adequacy studied in the present document.

See [Reconstruction of constitutive alignment](constitutive_alignment_reconstruction.md) for the complete development and its exact limits.'''
insert_before('docs/en/relative_alignment.md', '\n---\n\n## 7. Soundness', en_relative_block)

# README FR: selected results, source architecture, and documentation links.
replace_once(
    'README_fr.md',
    "| les carrés médiés adjacents se collent | `Alignment.MediatedTransitionPasting` |\n| le statut diagonal n'est pas représentable intérieurement | `diagonalStatus_notRepresentable` |",
    "| les carrés médiés adjacents se collent | `Alignment.MediatedTransitionPasting` |\n| préserver toute la genèse caractérise les transports relevés depuis la base | `Alignment.GenesisReconstruction.preservesGenesis_iff_reconstructible` |\n| le matching ancré total reconstruit un transport exact | `Alignment.GenesisReconstruction.TotalAnchoredMatching.toExactTransport` |\n| la recherche enumerable classe quatre régimes d'alignabilité | `Alignment.GenesisReconstruction.FiniteAlignmentClassification.classify` |\n| un matching directionnel persiste injectivement pour tout `n : Nat` | `Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteForwardEmbeddingOfMatching` |\n| le statut diagonal n'est pas représentable intérieurement | `diagonalStatus_notRepresentable` |")

replace_once(
    'README_fr.md',
    "- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)  \n  ajoute les lectures en aval de l'identité et démontre la persistance des distinctions déjà établies.\n\n- [`MediatedTransitionCoherence.lean`](MediatedTransitionCoherence.lean)",
    "- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)  \n  ajoute les lectures en aval de l'identité et démontre la persistance des distinctions déjà établies.\n\n- [`Alignment/GenesisReconstruction.lean`](Alignment/GenesisReconstruction.lean) et [`Alignment/GenesisCharacterization.lean`](Alignment/GenesisCharacterization.lean)  \n  reconstruisent le transport initial depuis la préservation de la genèse et caractérisent exactement les transports ainsi relevés.\n\n- [`Alignment/GenesisRigidity.lean`](Alignment/GenesisRigidity.lean), [`Alignment/ConstitutiveProfileRigidity.lean`](Alignment/ConstitutiveProfileRigidity.lean) et [`Alignment/ConstitutiveProfileReconstruction.lean`](Alignment/ConstitutiveProfileReconstruction.lean)  \n  localisent l'ambiguïté à la base puis la contraignent par des profils constitutifs séparants.\n\n- [`Alignment/AnchoredRelationReconstruction.lean`](Alignment/AnchoredRelationReconstruction.lean), [`Alignment/AnchoredMatchReconstruction.lean`](Alignment/AnchoredMatchReconstruction.lean) et [`Alignment/AnchoredMatchStrictness.lean`](Alignment/AnchoredMatchStrictness.lean)  \n  dérivent les profils de relations ancrées, reconstruisent le matching structurel et distinguent inclusion directionnelle et alignement exact.\n\n- [`Alignment/FiniteAnchoredMatchSearch.lean`](Alignment/FiniteAnchoredMatchSearch.lean), [`Alignment/FiniteAnchoredMatchDecision.lean`](Alignment/FiniteAnchoredMatchDecision.lean) et [`Alignment/FiniteAlignmentClassification.lean`](Alignment/FiniteAlignmentClassification.lean)  \n  rendent la recherche executable sur des enumerations finies complètes, prouvent sa complétude et classent les quatre régimes d'alignabilité.\n\n- [`Alignment/DirectionalGenesisPersistence.lean`](Alignment/DirectionalGenesisPersistence.lean)  \n  propage canoniquement les matchings directionnels comme plongements injectifs à toute profondeur `n : Nat`.\n\n- [`MediatedTransitionCoherence.lean`](MediatedTransitionCoherence.lean)")

replace_once(
    'README_fr.md',
    "- [Instance circulaire — alignement relatif](docs/fr/alignement_relatif.md)\n- [Méthode des rôles constitutifs relationnels](docs/fr/methode_roles_constitutifs_relationnels.md)",
    "- [Instance circulaire - alignement relatif](docs/fr/alignement_relatif.md)\n- [Reconstruction de l'alignement constitutif](docs/fr/reconstruction_alignement_constitutif.md)\n- [Méthode des rôles constitutifs relationnels](docs/fr/methode_roles_constitutifs_relationnels.md)")

insert_before(
    'README_fr.md',
    "La persistance est quantifiée uniformément pour toute profondeur cible `n : Nat` arbitraire, sans profondeur maximale fixée.",
    "La branche de reconstruction de l'alignement ne suppose plus un carrier initial commun d'identités. Elle reste toutefois relative à un contexte relationnel ancré fourni. Dans sa couche de décision executable, elle suppose en outre des enumerations finies complètes des carriers et des ancres. La reconstruction automatique de la famille d'ancres elle-même reste ouverte.")

# README EN.
replace_once(
    'README.md',
    "| natural-depth indexing, extension, transport, composition and naturality | [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) |\n| readouts after constitution | [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean) |",
    "| natural-depth indexing, extension, transport, composition and naturality | [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) |\n| reconstruction from genesis | [`Alignment/GenesisReconstruction.lean`](Alignment/GenesisReconstruction.lean), [`Alignment/GenesisCharacterization.lean`](Alignment/GenesisCharacterization.lean) |\n| rigidity and separating constitutive profiles | [`Alignment/GenesisRigidity.lean`](Alignment/GenesisRigidity.lean), [`Alignment/ConstitutiveProfileRigidity.lean`](Alignment/ConstitutiveProfileRigidity.lean) |\n| reconstruction from anchored relations and matching | [`Alignment/AnchoredRelationReconstruction.lean`](Alignment/AnchoredRelationReconstruction.lean), [`Alignment/AnchoredMatchReconstruction.lean`](Alignment/AnchoredMatchReconstruction.lean) |\n| executable search, decision, and four-regime classification | [`Alignment/FiniteAnchoredMatchSearch.lean`](Alignment/FiniteAnchoredMatchSearch.lean), [`Alignment/FiniteAnchoredMatchDecision.lean`](Alignment/FiniteAnchoredMatchDecision.lean), [`Alignment/FiniteAlignmentClassification.lean`](Alignment/FiniteAlignmentClassification.lean) |\n| directional genesis persistence | [`Alignment/DirectionalGenesisPersistence.lean`](Alignment/DirectionalGenesisPersistence.lean) |\n| readouts after constitution | [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean) |")

insert_before(
    'README.md',
    'The persistence results are uniform for every `n : Nat` and impose no fixed maximum depth.',
    "The alignment-reconstruction branch no longer assumes a common initial identity carrier. It remains relative to a supplied anchored relational context. Its executable decision layer additionally assumes complete finite enumerations of the carriers and anchors. Automatic reconstruction of the anchor family itself remains open.")

replace_once(
    'README.md',
    "- [Relative alignment](docs/en/relative_alignment.md)\n- [Alignement relatif](docs/fr/alignement_relatif.md)",
    "- [Relative alignment](docs/en/relative_alignment.md)\n- [Constitutive alignment reconstruction](docs/en/constitutive_alignment_reconstruction.md)\n- [Alignement relatif](docs/fr/alignement_relatif.md)\n- [Reconstruction de l'alignement constitutif](docs/fr/reconstruction_alignement_constitutif.md)")

# Architecture maps: expose the new linear reconstruction branch.
fr_arch = r'''### Reconstruction de l'alignabilité constitutive

Une nouvelle chaîne générique part de `Alignment.FinitePersistence` et ne dépend pas de l'instance circulaire :

```text
Alignment.FinitePersistence
        ↓
Alignment.GenesisReconstruction
        ↓
Alignment.GenesisCharacterization
        ↓
Alignment.GenesisRigidity
        ↓
Alignment.ConstitutiveProfileRigidity
        ↓
Alignment.ConstitutiveProfileReconstruction
        ↓
Alignment.AnchoredRelationReconstruction
        ↓
Alignment.AnchoredMatchReconstruction
        ↓
Alignment.AnchoredMatchStrictness
        ↓
Alignment.FiniteAnchoredMatchSearch
        ↓
Alignment.FiniteAnchoredMatchDecision
        ↓
Alignment.FiniteAlignmentClassification
        ↓
Alignment.DirectionalGenesisPersistence
```

Cette branche reconstruit d'abord le transport initial depuis la préservation de la genèse, localise l'ambiguïté restante à la base, puis la contraint par des profils relationnels ancrés. Dans le cas enumerable, elle recherche et décide les matchings directionnels, distingue quatre régimes et propage canoniquement les injections justifiées à tout `n : Nat`.

Elle ne suppose pas de carrier initial commun d'identités. Elle suppose encore une famille d'ancres correspondantes et des relations locales permettant de séparer les identités.

Voir [Reconstruction de l'alignement constitutif](reconstruction_alignement_constitutif.md).'''
insert_before('docs/fr/cartographie_architecturale_verifiee.md', '### `RepresentationBoundary.DiagonalizationKernel`', fr_arch)

en_arch = r'''### Reconstruction of constitutive alignability

A new generic chain starts from `Alignment.FinitePersistence` and does not depend on the circular instance:

```text
Alignment.FinitePersistence
        ↓
Alignment.GenesisReconstruction
        ↓
Alignment.GenesisCharacterization
        ↓
Alignment.GenesisRigidity
        ↓
Alignment.ConstitutiveProfileRigidity
        ↓
Alignment.ConstitutiveProfileReconstruction
        ↓
Alignment.AnchoredRelationReconstruction
        ↓
Alignment.AnchoredMatchReconstruction
        ↓
Alignment.AnchoredMatchStrictness
        ↓
Alignment.FiniteAnchoredMatchSearch
        ↓
Alignment.FiniteAnchoredMatchDecision
        ↓
Alignment.FiniteAlignmentClassification
        ↓
Alignment.DirectionalGenesisPersistence
```

This branch first reconstructs initial transport from genesis preservation, localizes remaining ambiguity at the base, then constrains it through anchored relational profiles. In the enumerable case it searches for and decides directional matchings, distinguishes four regimes, and canonically propagates justified injections to every `n : Nat`.

It assumes no common initial identity carrier. It still assumes corresponding anchors and local relations sufficient to separate identities.

See [Reconstruction of constitutive alignment](constitutive_alignment_reconstruction.md).'''
insert_before('docs/en/verified_architecture_map.md', '### `RepresentationBoundary.DiagonalizationKernel`', en_arch)

# Scientific positioning FR: enrich alignment section and formal-anchor list.
insert_before(
    'POSITIONNEMENT_SCIENTIFIQUE.md',
    "La chaîne complète est donc :",
    "La branche de reconstruction approfondit maintenant ce point. Entre deux carriers initiaux distincts, la préservation de toute la genèse caractérise exactement les transports terminaux qui proviennent du relevement d'un transport initial. L'ambiguïté restante est alors localisée à la base. Des profils constitutifs séparants, puis des profils dérivés de relations à des ancres correspondantes, rendent le matching initial unique lorsqu'il existe. Dans le cas enumerable, le dépôt recherche effectivement ces correspondances, décide leur totalité dans chaque direction et classe le contexte en quatre régimes : `exact`, `forwardOnly`, `backwardOnly` ou `noDirectionalMatching`.\n\nCette couche constitue une reconstruction relative de l'alignabilité. Elle ne reconstruit pas encore automatiquement la famille d'ancres elle-même depuis deux systèmes qui seraient fournis sans médiateur relationnel commun.")

replace_once(
    'POSITIONNEMENT_SCIENTIFIQUE.md',
    "- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) pour la persistance uniforme pour tout `n : Nat` et la naturalité des transports\n- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean) pour les contre-exemples montrant que l'exactitude seule ne suffit pas à la cohérence",
    "- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) pour la persistance uniforme pour tout `n : Nat` et la naturalité des transports\n- [`Alignment/GenesisReconstruction.lean`](Alignment/GenesisReconstruction.lean) et [`Alignment/GenesisCharacterization.lean`](Alignment/GenesisCharacterization.lean) pour la reconstruction depuis la genèse\n- [`Alignment/AnchoredMatchReconstruction.lean`](Alignment/AnchoredMatchReconstruction.lean) pour la reconstruction du matching initial depuis les observations relationnelles ancrées\n- [`Alignment/FiniteAlignmentClassification.lean`](Alignment/FiniteAlignmentClassification.lean) pour la classification executable des quatre régimes d'alignabilité\n- [`Alignment/DirectionalGenesisPersistence.lean`](Alignment/DirectionalGenesisPersistence.lean) pour la persistance directionnelle canonique à tout `n : Nat`\n- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean) pour les contre-exemples montrant que l'exactitude seule ne suffit pas à la cohérence")

# Scientific positioning EN: corresponding changes.
insert_before(
    'SCIENTIFIC_POSITIONING.md',
    'The complete chain is therefore:',
    "The reconstruction branch now deepens this point. Between two distinct initial carriers, preservation of the whole genesis stratification exactly characterizes terminal transports that arise by lifting an initial transport. The remaining ambiguity is thereby localized at the base. Separating constitutive profiles, then profiles derived from relations to corresponding anchors, make the initial matching unique when it exists. In the enumerable case the repository effectively searches for these correspondences, decides their totality in each direction, and classifies the context into four regimes: `exact`, `forwardOnly`, `backwardOnly`, or `noDirectionalMatching`.\n\nThis layer is a relative reconstruction of alignability. It does not yet automatically reconstruct the anchor family itself from two systems supplied without a shared relational mediator.")

replace_once(
    'SCIENTIFIC_POSITIONING.md',
    "- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) for persistence uniform over every `n : Nat` and transport naturality\n- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean) for counterexamples showing that exactness alone does not imply coherence",
    "- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) for persistence uniform over every `n : Nat` and transport naturality\n- [`Alignment/GenesisReconstruction.lean`](Alignment/GenesisReconstruction.lean) and [`Alignment/GenesisCharacterization.lean`](Alignment/GenesisCharacterization.lean) for reconstruction from genesis\n- [`Alignment/AnchoredMatchReconstruction.lean`](Alignment/AnchoredMatchReconstruction.lean) for reconstruction of initial matching from anchored relational observations\n- [`Alignment/FiniteAlignmentClassification.lean`](Alignment/FiniteAlignmentClassification.lean) for executable four-regime classification of alignability\n- [`Alignment/DirectionalGenesisPersistence.lean`](Alignment/DirectionalGenesisPersistence.lean) for canonical directional persistence at every `n : Nat`\n- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean) for counterexamples showing that exactness alone does not imply coherence")

# Add new documentation files to the scientific manifest and recompute every listed hash.
manifest = Path('MANIFEST.sha256')
entries = []
for line in manifest.read_text(encoding='utf-8').splitlines():
    if not line.strip():
        continue
    _digest, filename = line.split('  ', 1)
    entries.append(filename)
for filename in [
    'docs/fr/reconstruction_alignement_constitutif.md',
    'docs/en/constitutive_alignment_reconstruction.md',
]:
    if filename not in entries:
        entries.append(filename)

lines = []
for filename in entries:
    data = Path(filename).read_bytes()
    lines.append(f'{hashlib.sha256(data).hexdigest()}  {filename}')
manifest.write_text('\n'.join(lines) + '\n', encoding='utf-8')

print('alignment documentation updated')
