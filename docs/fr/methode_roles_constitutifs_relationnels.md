# Méthode des rôles constitutifs relationnels

*Individuation, minimisation des primitives, transport fidèle et diagnostic normatif*

[English](../en/relational_constitutive_roles_method.md) | **Français**

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d'OpenAI, sous direction humaine et au cours
> d'interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[Cycle 1 — alignement relatif](alignement_relatif.md) ·
[Cycle 2 — alignement réflexif](alignement_reflexif.md)

> **Ce document expose la méthode dégagée par le cycle 1 : individuer les
> occurrences avant leurs lectures, déterminer leurs rôles par les relations qui
> les constituent, éprouver l'indépendance des propriétés sur des carriers
> affaiblis, puis reconstruire et transporter uniquement les déterminations dont
> la conservation a été démontrée.** Appliquée à l'alignement relatif, cette
> méthode permet de localiser une rupture normative sur une construction qui
> continue d'exister et de rester fidèlement réalisable.

Documents complémentaires :

- [preuve formelle d'alignement relatif — français](alignement_relatif.md) ;
- [formal proof of relative alignment — English](../en/relative_alignment.md) ;
- [fondements structurels — français](fondements_structurels.md) ;
- [structural foundations — English](../en/structural_foundations.md) ;
- [alignement réflexif — français](alignement_reflexif.md) ;
- [reflective alignment — English](../en/reflective_alignment.md).

## Résumé

Une formalisation perd sa capacité diagnostique lorsqu'elle identifie trop tôt
une occurrence à sa lecture, une position à une participation, une couverture à
une exhaustivité, ou une construction possible à une construction admissible.
La méthode des rôles constitutifs relationnels organise la conception d'un
formalisme de manière à empêcher ces effondrements.

Elle part d'occurrences dépendamment typées, constituées par une formation et
inscrites dans des relations de provenance, de source, de cible, de succession
et de composition. Elle exprime ensuite la réalisation d'une exigence par un
accord structurel exact et injectif. Pour déterminer quelles propriétés doivent
être primitives, elle affaiblit volontairement le carrier et construit des
modèles séparateurs : une trace permutée conserve l'exactitude locale sans
conserver l'ordre ; une trace intercalée conserve l'exactitude et l'ordre sans
garantir la participation à une composition constitutive. Lorsque la
composabilité réelle des histoires est réintroduite, la précédence et
l'adjacence deviennent dérivables.

La même discipline gouverne le changement de représentation. Une réalisation
concrète fidèle ne se réduit pas à une fonction d'évaluation : elle fournit des
correspondances inverses entre occurrences ainsi que les accords sur leurs pas,
leurs sources et leurs cibles. Les invariants cardinaux et numériques sont alors
lus comme des conséquences de cette conservation structurelle.

Enfin, la méthode sépare construction, réalisation, régime et norme. Une norme
est définie indépendamment du régime chargé de l'appliquer ; leur adéquation est
prouvée dans les deux directions ; puis une sortie typée conserve le candidat et
ses témoins positifs de fidélité tout en portant la réfutation de son admission.
Dans l'application circulaire, `oneStepAfterPerimeter` est exactement un tel
témoin : continuation stricte, réalisation locale exacte, réalisation concrète
exacte pour toute algèbre fournie, mais rejet par le régime et insatisfaction
directe de la norme.

La contribution méthodologique n'est donc pas une nouvelle étiquette pour une
preuve particulière. C'est une procédure de conception et d'audit :

```text
individuer
→ relier
→ séparer
→ reconstruire
→ transporter
→ diagnostiquer
```

## Architecture du document

Le raisonnement est organisé en cinq parties complémentaires :

| Partie | Sections | Fonction |
|---|---:|---|
| **Fondations** | 1 à 6 | délimiter la méthode, ses statuts, son vocabulaire et l'accord exact entre rôle et occurrence |
| **Séparation et reconstruction** | 7 à 10 | tester les dépendances sur des carriers affaiblis, puis reconstruire ordre, adjacence et participation |
| **Conservation** | 11 et 12 | définir le transport fidèle et dériver les invariants structurels et numériques |
| **Diagnostic normatif** | 13 et 14 | séparer norme et régime, prouver leur adéquation et résumer le témoin canonique |
| **Réemploi et audit** | 15 à 20 | fournir un protocole, des critères d'échec, une portée explicite et les ancrages Lean |

Les sections 1 à 14 reconstruisent l'argument. Les sections 15 à 19 transforment
cet argument en procédure réutilisable et vérifiable. La conclusion en condense
le principe directeur.

## 1. Objet de la méthode

La méthode répond à la question suivante :

> Comment déterminer formellement ce qui constitue une occurrence, ce qu'une
> réalisation doit en préserver, quelles propriétés sont primitives ou
> dérivées, et où une construction cesse de satisfaire une norme sans cesser
> d'être constructible ?

Elle vise les situations dans lesquelles plusieurs niveaux risquent d'être
confondus : l'objet construit, sa représentation, son évaluation et son statut
normatif. Ces niveaux peuvent coïncider sur un exemple sans être identiques. Une
méthode rigoureuse doit conserver leur distinction assez longtemps pour rendre
leurs rapports démontrables.

Le cycle 1 fournit une instance complète de cette démarche. Il contient :

- un langage de constructions libres ;
- des occurrences individuées dans des histoires ;
- des exigences périmétrales réalisées exactement ;
- des carriers affaiblis servant à tester l'indépendance de certaines
  propriétés ;
- des interprétations concrètes qui conservent les occurrences ;
- un régime opérationnel ;
- une norme autonome ;
- des théorèmes de soundness et de complétude ;
- une sortie minimale conservant sa fidélité tout en perdant son statut
  normatif.

La méthode n'est pas limitée au vocabulaire de la circularité. En revanche, son
application complète n'est actuellement vérifiée en Lean que pour les
structures du cycle 1. Le passage d'une instance formelle à une méthode
réutilisable exige donc de distinguer soigneusement preuve, extraction
méthodologique et généralisation proposée.

## 2. Statut des énoncés

Quatre statuts sont employés dans ce document.

| Statut | Signification | Exemple |
|---|---|---|
| **Vérifié dans Lean** | définition, construction ou théorème présent dans les modules du cycle 1 | `ExactNonClosingRealization.preservesNext` |
| **Conséquence dérivée** | composition explicite de résultats Lean vérifiés | deux réalisations exactes d'une même histoire conservent la même structure d'occurrences via l'histoire libre commune |
| **Extraction méthodologique** | règle de conception justifiée par l'organisation des définitions, preuves et modèles séparateurs | affaiblir le carrier pour tester si une propriété est primitive |
| **Généralisation proposée** | principe destiné à d'autres domaines, mais non encore démontré comme métathéorème universel | employer la méthode pour toute architecture d'alignement |

Les passages entre ces niveaux ne doivent jamais rester implicites. Un théorème
sur `RootedGeneratedHistory P` ne devient pas, par reformulation, un théorème sur
tout système dynamique. Réciproquement, le fait qu'un principe méthodologique
ne soit pas un théorème universel n'annule pas son contenu : sa justification
peut reposer sur une instance vérifiée, sur des contre-modèles effectifs et sur
la reconstruction précise des dépendances.

Le document suit donc la convention suivante :

```text
déclaration Lean nommée
  → fait formel vérifié

composition indiquée de déclarations Lean
  → conséquence dérivée

règle de construction extraite de cette organisation
  → proposition méthodologique

extension à un autre domaine ou à un carrier plus général
  → programme de généralisation
```

Cette convention permet de formuler la méthode avec force sans attribuer au
noyau Lean une portée qu'il n'a pas encore.

## 3. Vocabulaire structurel

La méthode repose sur un vocabulaire dont les niveaux doivent rester distincts.

### 3.1 Présentation

Une présentation fixe les types et les règles à partir desquels des
constructions peuvent être formées. Dans l'application du cycle 1,
`CircularPresentation` fournit notamment les types explicites et implicites, les
compatibilités, les différences, les provenances, le périmètre et l'obstruction
à la boucle totale.

La présentation ne classe pas encore toutes les histoires comme admises ou
rejetées. Elle fournit les conditions de leur constitution.

### 3.2 Constitution et formation

Une constitution est un objet dont la construction enregistre les données qui
l'ont formé. `FreeConstitution` ne représente pas seulement une valeur atteinte :
elle préserve la structure nécessaire pour retrouver la formation, la
provenance et l'obstruction transportée.

La formation répond à la question :

```text
par quel acte typé cet objet a-t-il été constitué ?
```

Elle précède les lectures externes qui pourront ensuite lui être appliquées.

### 3.3 Pas et occurrence

Un `GeneratedStep` relie une source et une cible selon les règles de la
présentation. Une occurrence est une apparition individuée d'un tel pas dans
une `History`.

La distinction est essentielle : deux occurrences peuvent porter des pas dont
les lectures coïncident tout en restant des positions différentes dans
l'histoire. `History.Occurrence` conserve cette individuation.

### 3.4 Rôle constitutif relationnel

Un **rôle constitutif relationnel** est la détermination d'une occurrence par les
relations structurelles dans lesquelles elle intervient au sein d'une
constitution.

Le terme *constitutif* signifie que ces relations contribuent à déterminer ce
qu'est l'occurrence dans la construction étudiée. Le terme *relationnel* signifie
que le rôle ne se réduit pas à une propriété isolée ou à une étiquette portée
par l'occurrence.

Schématiquement :

```text
Role(P, H, r, o)
```

où :

- `P` est la présentation ;
- `H` est l'histoire constituée ;
- `r` est l'exigence ou la position structurelle attendue ;
- `o` est l'occurrence qui réalise ce rôle.

Le rôle peut dépendre simultanément de :

```text
formation(o)
provenance(o)
source(o)
cible(o)
position(o, H)
succession(o, H)
participation(o, composition)
accord(o, r)
```

Cette notation est une présentation méthodologique, non une nouvelle
déclaration Lean. Dans le cycle 1, son contenu est réalisé par plusieurs types
et relations plutôt que par une structure unique nommée `Role`.

### 3.5 Carrier (type porteur)

Le carrier — ou type porteur — est le type d'objets sur lequel une propriété est
étudiée. Changer de carrier change les relations disponibles et donc ce qui peut
être démontré.

Une `SemanticTrace` et une `RootedGeneratedHistory` peuvent porter des pas
similaires, mais seule la seconde impose la composabilité globale d'une histoire
générée. Le choix du carrier n'est donc pas un détail de représentation : il
fait partie des hypothèses du raisonnement.

## 4. Les effondrements que la méthode doit empêcher

Le besoin méthodologique apparaît lorsqu'une abstraction correcte pour une
tâche devient destructrice pour une autre. Quatre effondrements sont
particulièrement importants.

### 4.1 Lecture et occurrence

Une lecture associe une valeur à une occurrence :

```text
ρ : Occurrence → Value
```

L'égalité `ρ(x) = ρ(y)` ne suffit pas à conclure `x = y`. Les deux occurrences
peuvent différer par leur formation, leur provenance, leur position ou leur rôle
dans une composition. Les identifier par leur lecture détruirait précisément
les données nécessaires à l'audit de leur trajectoire.

Le problème n'est pas l'usage d'une lecture. Il est son emploi rétroactif comme
principe d'individuation. Une lecture peut être pertinente après la construction
de l'occurrence ; elle ne doit pas remplacer sans preuve les relations qui ont
constitué cette occurrence.

### 4.2 Position et participation

Une occurrence peut être située entre deux autres dans une liste sans participer
à une histoire générée qui relie leurs états. La relation d'ordre renseigne sur
la position ; la participation constitutive exige une correspondance avec les
occurrences d'une composition effectivement typée.

```text
position intermédiaire
≠ occurrence d'un pont constitutif
```

Confondre ces notions permettrait de traiter toute donnée intercalée comme une
partie de la construction qui joint ses voisines, alors que ses sources, ses
cibles ou son mode de génération peuvent être incompatibles avec cette
composition.

### 4.3 Couverture et exhaustivité

Réaliser exactement toutes les exigences d'une localité ne signifie pas que
l'histoire ne contient rien d'autre.

```text
chaque exigence possède un témoin exact
≠
chaque occurrence est le témoin d'une exigence
```

La première proposition est une couverture. La seconde est une classification
exhaustive. Les identifier interdirait par définition toute continuation au-delà
du domaine couvert et ferait disparaître le phénomène que l'analyse cherche à
diagnostiquer.

### 4.4 Constructibilité et admissibilité

Un générateur peut produire un pas que le régime rejette. Cette situation n'est
ni contradictoire ni incomplète si construction et régime ont été définis
séparément.

```text
Constructible(x)
≠ Admissible(x)
```

L'effondrement des deux notions transforme toute sortie de régime soit en
impossibilité de construire, soit en erreur non localisée. Leur séparation
permet au contraire de conserver l'objet produit, les propriétés qu'il satisfait
encore et la preuve de la propriété exacte qu'il ne satisfait plus.

## 5. Ordre de dépendance

La méthode impose un ordre de construction destiné à rendre chaque dépendance
auditable.

```text
présentation
→ formations possibles
→ occurrences individuées
→ accords entre exigences et occurrences
→ succession et composition
→ invariants structurels internes
→ réalisations concrètes et preuves de conservation
→ lectures numériques dérivées
→ normes indépendantes et régimes opérationnels définis séparément
→ preuves d'adéquation
→ diagnostics
```

Cet ordre n'affirme pas que toute théorie doive employer exactement les types du
cycle 1. Il énonce une discipline : ne pas utiliser une couche ultérieure pour
définir silencieusement une couche antérieure.

### 5.1 Individuation avant lecture

La lecture suppose un domaine d'occurrences déjà constitué. Si elle sert à
définir ce domaine, l'égalité des lectures fusionne par construction les
occurrences que l'analyse aurait peut-être dû distinguer.

### 5.2 Composition avant temps global

Dans le cycle 1, l'antériorité vient de la structure de préfixe et la globalité
de la composition des histoires. Aucune horloge extérieure n'est nécessaire
pour créer après coup l'ordre des pas.

### 5.3 Fidélité avant invariants numériques

Une égalité de cardinalités peut masquer une permutation, une fusion suivie d'un
ajout ou une perte compensée. L'équivalence des occurrences et les accords
structurels doivent être établis avant que leur cardinalité soit lue comme un
invariant significatif.

### 5.4 Norme avant adéquation du régime

Si la norme est définie comme « ce que le régime accepte », la soundness devient
tautologique et la complétude perd sa fonction critique. L'autonomie de la norme
est une condition de possibilité du diagnostic d'alignement relatif.

## 6. Réaliser exactement un rôle

La réalisation d'un rôle doit préciser ce qui est conservé entre une exigence et
une occurrence.

### 6.1 Trois niveaux d'accord

On peut distinguer :

```text
1. accord d'étiquette
2. accord partiel sur certaines projections
3. accord structurel exact
```

Un accord d'étiquette affirme seulement qu'une occurrence a reçu le nom du rôle.
Un accord partiel compare, par exemple, sa source ou sa valeur. Un accord exact
porte sur une donnée structurelle suffisamment fine pour que les accords utiles
puissent en être dérivés.

Dans l'application périmétrale, `RequirementOccurrenceAgreement` demande :

```lean
occurrence.locatedStep =
  positionLocatedStep P FreeConstitution.root
    BoundaryDifference.initial position
```

L'égalité concerne le `LocatedStep` complet. Les accords sur la source, la cible,
la compatibilité et la provenance sont ensuite obtenus par transport ou
projection. La méthode privilégie ainsi un noyau exact dont les conséquences
restent calculables, plutôt qu'une collection d'accords faibles sans principe
commun.

### 6.2 Couverture exacte et injective

`ExactNonClosingRealization P history` contient :

```text
realize
  : NonClosingPosition P.perimeter
  → History.Occurrence history.history

realize_injective
  : Function.Injective realize

agreement
  : chaque position est en accord exact avec son occurrence
```

Les trois champs jouent des rôles différents :

- `realize` fournit un témoin pour chaque exigence ;
- `realize_injective` préserve la distinction des exigences dans les
  occurrences ;
- `agreement` établit que les témoins ne sont pas arbitraires.

Omettre l'injectivité autoriserait plusieurs exigences à être absorbées par la
même occurrence. Omettre l'accord autoriserait une injection sans contenu
structurel. Omettre la fonction de réalisation réduirait l'énoncé à une
propriété globale sans témoins accessibles.

### 6.3 Pourquoi l'exactitude n'implique pas l'exhaustivité

La structure ne contient pas de fonction inverse classant toute occurrence
comme une exigence non fermante. Cette omission est intentionnelle.

```text
exigences → occurrences
```

n'est pas remplacé par :

```text
exigences ⇄ toutes les occurrences de l'histoire
```

Une histoire peut donc contenir les réalisations exactes attendues et une
continuation supplémentaire. Cette ouverture est nécessaire pour formuler le
candidat `oneStepAfterPerimeter` sans nier la réalisation correcte du périmètre
qu'il contient.

## 7. Minimiser les primitives

Une formalisation robuste doit distinguer les propriétés véritablement
indépendantes de celles qui sont seulement difficiles à démontrer dans la
présentation courante.

La méthode procède ici par expérimentation formelle : elle modifie les
hypothèses, construit des modèles séparateurs et observe quelles propriétés
survivent.

### 7.1 Proposer une détermination candidate

On part d'une propriété dont le statut est incertain :

- ordre des occurrences ;
- adjacence ;
- contiguïté ;
- participation à une composition ;
- exhaustivité ;
- conservation sous interprétation.

La question n'est pas seulement « peut-on la prouver ? », mais :

> De quelles structures dépend exactement cette propriété ?

### 7.2 Affaiblir le carrier

Un carrier affaibli doit retirer la structure suspectée de produire la propriété
sans détruire les couches déjà établies.

`SemanticTrace` conserve une liste de `LocatedStep` générés et individue les
occurrences par leurs indices. Elle permet donc de conserver :

- les données locales complètes des pas ;
- la distinction des occurrences ;
- une réalisation locale exacte et injective.

Elle retire cependant la composabilité globale exigée par `History`.

### 7.3 Construire un modèle séparateur

Un modèle séparateur satisfait les propriétés plus faibles tout en réfutant la
propriété candidate. Sa fonction n'est pas de simuler tout le système, mais de
montrer qu'une implication supposée ne provient pas des seules hypothèses
annoncées.

```text
structure faible W
+ propriété A vérifiée dans W
+ propriété B réfutée dans W
→ A ne suffit pas à déterminer B à ce niveau
```

### 7.4 Réintroduire la structure

Une fois l'indépendance établie sur le carrier faible, on réintroduit les
contraintes réelles de construction. Deux résultats sont alors possibles :

1. la propriété reste indépendante et doit être ajoutée explicitement ;
2. elle devient dérivable à partir de la structure réintroduite.

Le deuxième cas est méthodologiquement important. Il évite d'ajouter comme
primitive une propriété déjà imposée par une composabilité plus fondamentale.

### 7.5 Critère de minimalité

Une primitive est justifiée lorsque :

- la propriété est nécessaire à l'usage visé ;
- elle n'est pas reconstructible à partir des primitives conservées ;
- un modèle séparateur montre l'indépendance de la propriété au niveau plus
  faible ;
- son ajout ne réintroduit pas implicitement une couche que la méthode cherche à
  analyser séparément.

L'absence de contre-modèle dans un langage déjà trop contraint ne constitue pas
une preuve de primitivité.

## 8. Deux modèles séparateurs

Les traces permutée et intercalée du cycle 1 ne sont pas de simples exemples
pédagogiques. Elles jouent des rôles logiques distincts dans l'analyse des
dépendances.

### 8.1 Trace permutée : exactitude sans ordre

La trace :

```text
p2, p1, p3
```

conserve les trois pas canoniques mais inverse les deux premières occurrences.
`permutedExampleRealization` fournit néanmoins une réalisation locale exacte et
injective. Le théorème `permutedExample_not_order_preserved` réfute
`SemanticOrderPreserved` pour cette réalisation.

La séparation obtenue est :

```text
exactitude locale
+ injectivité
⇏ ordre structurel
```

Elle montre que l'ordre ne peut pas être extrait du seul accord local sur le
carrier `SemanticTrace`.

### 8.2 Trace intercalée : ordre sans participation

La trace :

```text
p1, extra1, p2, extra2, p3
```

conserve les exigences canoniques dans leur ordre. Le résultat
`interleavedExample_order_preserved` établit explicitement cette conservation.
Des occurrences supplémentaires sont néanmoins placées entre les réalisations
canoniques.

`SemanticTrace.Between` suffit à exprimer leur position. Pour exprimer leur
participation à une composition générée, `ExactSemanticBridgeSegment` exige des
correspondances inverses avec les occurrences d'un `GeneratedHistory`, ainsi que
l'accord exact des pas localisés. `EffectiveConstitutiveBridge` assemble ce
segment en un pont constitutif avec les extrémités pertinentes.

Les théorèmes :

```lean
interleavedExample_no_effective_bridge_p1_p2
interleavedExample_no_effective_bridge_p2_p3
```

montrent que les occurrences intercalées ne constituent pas un pont effectif
entre les exigences canoniquement adjacentes.

La séparation obtenue est :

```text
exactitude locale
+ injectivité
+ ordre préservé
+ position intermédiaire
⇏ participation à une composition constitutive
```

### 8.3 Ce que les deux modèles établissent ensemble

Les deux traces forment une chaîne de séparation :

```text
accord exact
  n'impose pas l'ordre sur un carrier faible

accord exact + ordre
  n'imposent pas la participation constitutive

composition réelle d'une History
  fournit les contraintes nécessaires à la reconstruction
```

La méthode ne conclut donc pas que l'ordre ou l'adjacence sont toujours
primitifs. Elle localise le niveau où ils ne sont pas encore déterminés, puis
recherche la structure qui permet de les dériver.

## 9. Reconstruire l'ordre et l'adjacence

Le passage de `SemanticTrace` à `RootedGeneratedHistory` réintroduit la
composabilité dépendamment typée des pas. La cible d'un pas et la source du
suivant ne sont plus de simples données juxtaposées : elles participent à la
construction même de l'histoire.

### 9.1 Précédence

Dans une histoire réellement générée, une réalisation locale exacte ne peut pas
inverser deux exigences structurellement précédentes sans produire une boucle
impossible dans la relation stricte de futur des curseurs.

Le théorème :

```lean
ExactNonClosingRealization.preservesPrecedence
```

transforme une preuve de `NonClosingPrecedes` entre deux exigences en une preuve
de `History.OccurrencePrecedes` entre leurs occurrences réalisées.

```text
accord exact
+ injectivité
+ composabilité de l'histoire
+ irréflexivité du futur structurel
→ précédence correcte
```

L'ordre n'a donc pas besoin d'être ajouté comme champ à
`ExactNonClosingRealization` sur le carrier fort.

### 9.2 Adjacence

La précédence n'exclut pas à elle seule une lacune positive. Pour des exigences
canoniquement adjacentes, une telle lacune produirait cependant, après transport
des extrémités exactes, un futur strict d'un curseur vers lui-même.

Le théorème :

```lean
ExactNonClosingRealization.preservesNext
```

transforme `NonClosingNext` en `History.OccurrenceNext`.

```text
adjacence canonique des exigences
+ réalisation locale exacte dans une History
→ adjacence constitutive des occurrences
```

### 9.3 Résultat méthodologique

Les mêmes propriétés changent de statut selon le carrier :

| Propriété | `SemanticTrace` | `RootedGeneratedHistory` |
|---|---:|---:|
| accord local exact | exprimable | exprimable |
| individuation injective | exprimable | exprimable |
| précédence canonique | primitive supplémentaire | dérivée |
| adjacence canonique | non imposée | dérivée |
| composabilité constitutive | absente | constitutive du carrier |

Une primitive n'est donc jamais « primitive en soi ». Elle est primitive
relativement à un langage, à un carrier et aux déterminations déjà disponibles.

## 10. Participation constitutive et composition

La participation désigne le fait qu'une occurrence appartient effectivement à
la construction qui relie deux états. Elle ne se réduit ni à la proximité
visuelle dans une séquence ni à une comparaison numérique des positions.

### 10.1 Pourquoi la relation « entre » est insuffisante

`SemanticTrace.Between trace left right` est un sous-type d'indices satisfaisant :

```text
left < occurrence ∧ occurrence < right
```

Cette relation est exacte comme relation de position. Elle ne dit rien, à elle
seule, sur l'existence d'une `GeneratedHistory` entre la cible de `left` et la
source de `right`.

### 10.2 Certifier la participation

`ExactSemanticBridgeSegment` demande :

- une application des occurrences intermédiaires vers les occurrences du
  pont ;
- une application inverse ;
- les deux lois d'aller-retour ;
- l'accord des `LocatedStep`.

Cette structure distingue trois questions :

```text
l'occurrence est-elle positionnée dans l'intervalle ?
l'occurrence appartient-elle au pont généré ?
le pas qu'elle porte est-il exactement celui du pont ?
```

`EffectiveConstitutiveBridge` ajoute le pont typé entre les extrémités
sélectionnées. La participation devient alors une propriété de composition et
non une métaphore spatiale.

### 10.3 Règle de conception

Lorsqu'une analyse emploie des termes comme *segment*, *chaîne*, *trajectoire*,
*intervalle* ou *étape intermédiaire*, elle doit préciser si elle parle :

1. d'une position dans une représentation ;
2. d'un ordre abstrait ;
3. d'une participation à une composition effectivement construite.

Le passage de l'un à l'autre exige une preuve. Cette règle dépasse l'exemple
périmétral : elle s'applique à toute formalisation dans laquelle une séquence de
données peut être confondue avec une trajectoire valide.

## 11. Transport fidèle entre réalisations

Une construction formelle peut recevoir plusieurs interprétations concrètes.
La méthode doit alors préciser ce qui reste invariant lorsque la représentation
change.

### 11.1 Une évaluation n'est pas encore une réalisation fidèle

Une fonction :

```text
interpret : FreeObject → ConcreteObject
```

peut perdre, fusionner ou inventer des distinctions. Même si sa valeur finale
semble correcte, elle ne garantit pas que les occurrences de la construction
libre puissent être auditées dans la réalisation concrète.

La fidélité requise par le cycle 1 porte sur les histoires et leurs occurrences,
pas seulement sur leurs états terminaux.

### 11.2 Structure d'une interprétation exacte

`ExactHistoryInterpretation A freeHistory concreteHistory` contient :

```text
forwardOccurrence
  : occurrences libres → occurrences concrètes

backwardOccurrence
  : occurrences concrètes → occurrences libres

forwardBackward
  : retour après aller = identité libre

backwardForward
  : aller après retour = identité concrète

occurrenceAgreement
  : accord structurel pour chaque occurrence libre
```

Les lois d'aller-retour établissent une équivalence d'occurrences. Elles
excluent à la fois :

- la perte d'une occurrence libre ;
- la fusion de deux occurrences libres ;
- l'ajout d'une occurrence concrète sans correspondant libre.

### 11.3 Accord concret

`ConcreteOccurrenceAgreement` relie une occurrence libre et son occurrence
concrète par :

- l'égalité exacte de la source concrète avec l'interprétation de la source
  libre ;
- l'égalité exacte de la cible concrète avec l'interprétation de la cible libre ;
- l'égalité hétérogène du pas concret attendu ;
- le témoin `ConcreteStepAgreement` fourni par l'algèbre.

L'équivalence des occurrences ne flotte donc pas au-dessus des pas. Elle est
accompagnée des accords qui donnent son sens structurel.

### 11.4 Construction uniforme

Pour toute `ConcreteContinuationAlgebra P` fournie,
`exactlyInterpretHistory A history` construit l'interprétation exacte de toute
`GeneratedHistory`.

La conséquence méthodologique est :

> L'indépendance à l'implémentation ne signifie pas que toutes les
> implémentations possibles sont fidèles. Elle signifie que le même résultat est
> obtenu pour chaque implémentation qui satisfait explicitement l'interface de
> fidélité demandée.

Cette quantification est essentielle. Elle évite de transformer une preuve
conditionnelle sur une interface en affirmation absolue sur toute
implémentation imaginable.

### 11.5 Comparer deux réalisations concrètes

Si deux algèbres concrètes fournies réalisent exactement la même histoire libre,
chacune de leurs structures d'occurrences est équivalente à celle de l'histoire
libre. Elles conservent donc, par composition via ce carrier commun, la même
détermination d'occurrences.

Il s'agit d'une conséquence dérivée de deux appels à
`exactlyInterpretHistory`, et non du nom d'un théorème binaire supplémentaire.
Cette précision illustre la discipline générale du document : distinguer ce que
Lean nomme directement de ce que l'on obtient par composition de résultats
vérifiés.

## 12. Invariants et lectures numériques

La méthode place la détermination structurelle avant sa lecture quantitative.

### 12.1 Existence et unicité avant le nombre

Le théorème abstrait
`SegmentedResidualRole.positiveExtension_hasUniqueResidualOccurrence` établit
qu'une extension positive fidèlement segmentée possède une occurrence
résiduelle unique.

Dans l'application périmétrale, `positiveContinuation_exactlyOne` établit :

```text
History.ExactlyOne labelled.continuation
```

Le nombre `1` n'est pas posé comme donnée primitive. Il est la lecture cardinale
d'une preuve d'existence et d'unicité.

```text
structure segmentée fidèle
→ existence d'une occurrence résiduelle
→ unicité
→ cardinalité 1
```

### 12.2 Composition et longueur

`History.append` compose deux histoires en conservant leur raccordement typé.
`History.length_append` démontre ensuite :

```text
length (append firstHistory continuation)
  = length firstHistory + length continuation
```

L'additivité est une propriété de cette lecture de la composition. Elle ne
définit ni la composition ni la totalité de l'histoire.

### 12.3 Classification et égalité de longueur

`samePerimeter_length_eq` déduit de `CircularRefinement P history` que :

```text
history.history.length
  = (perimeterDeployment P).history.length
```

La preuve passe par la classification structurelle du régime, qui réduit
l'histoire au déploiement périmétral canonique. L'égalité numérique est donc une
conséquence de la classification ; elle ne sert pas à définir cette
classification.

### 12.4 Sens de « mesure structurelle »

Dans ce document, une mesure structurelle désigne une détermination portée par
des occurrences, des correspondances et des indexations avant son évaluation
numérique. Elle ne désigne pas une mesure sigma-additive sur une algèbre
d'ensembles.

La règle méthodologique est :

> Avant d'interpréter un nombre comme invariant, identifier la structure dont il
> est la lecture et démontrer que cette structure est conservée par les
> transformations considérées.

## 13. Du structurel au normatif

La méthode devient une méthode d'alignement relatif lorsqu'elle ajoute une norme
indépendante et un régime dont l'adéquation à cette norme doit être prouvée.

### 13.1 Quatre niveaux à séparer

Pour une histoire `H` et une algèbre `A` :

```text
Construction(H)
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

Ces niveaux répondent à quatre questions différentes :

| Niveau | Question |
|---|---|
| construction | l'objet peut-il être formé ? |
| réalisation fidèle | l'objet est-il conservé dans cette implémentation ? |
| régime | l'opérationnel admet-il cet objet ? |
| norme | l'objet satisfait-il la spécification indépendante ? |

Une sortie normative n'est visible que si ces questions n'ont pas été
identifiées par définition.

### 13.2 Définir une norme autonome

`CircularSpecificationSatisfaction P H` possède deux champs :

```text
local
  : ExactNonClosingRealization P H

trajectory
  : StrictConstitutivePrefix (perimeterDeployment P) H
    → P.TotalLoop
```

Le champ local demande la réalisation exacte des exigences non fermantes. Le
champ trajectoriel donne un sens indépendant à la fermeture : une continuation
stricte du déploiement périmétral devrait déterminer une boucle totale.

La définition ne mentionne pas `CircularRefinement`. Cette indépendance rend la
comparaison non tautologique.

### 13.3 Prouver l'adéquation

Trois résultats ferment la comparaison :

```text
R(H) → S(H)
  circularRefinement_soundSpecification

S(H) → H = perimeterDeployment P
  CircularSpecificationSatisfaction.eq_perimeter

S(H) → R(H)
  circularSpecification_complete
```

Le premier est la soundness du régime relativement à la norme. Le deuxième
classe le carrier de la norme. Le troisième utilise cette classification pour
transporter le témoin canonique du régime.

L'accord obtenu est extensionnel : norme et régime classent les mêmes histoires.
Leurs structures de témoins ne sont pas identifiées.

### 13.4 Classifier sans confondre les témoins

`ExactRegimeClassification` conserve deux transformations :

```text
Regime candidate → candidate = canonical
candidate = canonical → Regime candidate
```

Cette structure ne remplace pas les témoins du régime par une proposition
booléenne. Elle conserve les directions constructives nécessaires à leur usage
ultérieur.

### 13.5 Construire une sortie typée

`RegimeExit Faithful Regime` réunit sur le même carrier :

```text
candidate
faithful   : Faithful candidate
inadmissible : Regime candidate → False
```

Une sortie ne se réduit donc pas à `¬ Regime candidate`. Elle préserve un témoin
positif expliquant ce qui reste valide sur l'objet rejeté.

`UniformRegimeExit` spécialise la famille de fidélité à :

```text
(implementation : Implementation)
→ Faithful implementation candidate
```

Le candidat est choisi avant l'implémentation. Cette structure exprime une
uniformité que ne fournirait pas une famille de candidats dépendant chacun de
leur implémentation.

### 13.6 Relier la sortie à la norme

`NormativeAdequacy` sépare le type des spécifications de la famille des régimes.
Dans l'interface actuelle, son carrier est spécialisé aux
`RootedGeneratedHistory P`. `AdequateAlong` demande un témoin d'adéquation à
chaque occurrence de l'histoire.

Dans `circularNormativeAdequacy`, le contenu de l'adéquation est global et
constant sur cet index :

```text
(R H → S H) × (S H → R H)
```

`SpecRelativeHistoryExit` compose ensuite :

- une sortie de régime typée ;
- la fidélité du même candidat ;
- l'adéquation du régime à la norme le long des occurrences du candidat.

L'insatisfaction de la norme doit néanmoins rester démontrée. L'adéquation et le
rejet du régime peuvent permettre de la dériver dans certains cadres, mais la
méthode préfère conserver une preuve directe lorsqu'elle est disponible, afin de
localiser exactement l'obligation normative qui échoue.

## 14. Étude condensée du témoin canonique

Le candidat :

```text
h⁺ := oneStepAfterPerimeter P
```

condense la méthode sur un même objet. Les constructions et signatures
détaillées appartiennent à la [preuve du Cycle 1](alignement_relatif.md) ; le
document de méthode conserve seulement le schéma de dépendances nécessaire au
réemploi :

```text
continuation stricte construite
  `oneStepAfterPerimeterStrict`

+ réalisation locale exacte et ordre reconstruit
  `oneStepAfterPerimeter_nonClosingRealization`

+ réalisation concrète exacte dans toute algèbre fournie
  `oneStepUniformPerimetralRegimeExit`

+ adéquation exacte entre régime et norme indépendante
  `circularNormativeAdequacy`, `circularRefinement_adequateAlong`

+ rejet opérationnel
  `oneStepAfterPerimeter_notCircularRefinement`

+ échec direct de l'obligation trajectorielle
  `oneStepAfterPerimeter_notSpecificationSatisfaction`

= diagnostic relatif conservant les preuves positives et négatives
  `oneStepSpecRelativeHistoryExit`
```

Le candidat reste construit, localement exact, correctement ordonné et
fidèlement réalisable. Ce qui est perdu est l'admission opérationnelle et
l'obligation normative trajectorielle. La conservation de cette information
positive transforme la réfutation en diagnostic structurel.

## 15. Protocole de réemploi

La méthode peut être appliquée à un nouveau domaine au moyen du protocole
suivant. Chaque phase possède une question, une sortie attendue et un risque
caractéristique.

### Phase 1 — Délimiter la présentation

**Question.** Quelles sont les données primitives et les règles de formation ?

**Sortie.** Un type de présentation et des constructeurs qui n'emploient pas
encore la classification normative finale.

**Risque.** Encoder le régime attendu directement dans les règles de
construction et rendre toute sortie impossible par définition.

### Phase 2 — Individuer les occurrences

**Question.** Qu'est-ce qui fait de deux apparitions deux occurrences distinctes ?

**Sortie.** Un type d'occurrences indexé par la construction qui conserve
position, formation ou provenance selon les besoins de l'audit.

**Risque.** Quotienter les occurrences par une lecture trop pauvre.

### Phase 3 — Définir les rôles attendus

**Question.** Quelles exigences locales la construction doit-elle réaliser ?

**Sortie.** Un type de rôles ou de positions structurelles indépendant des
occurrences qui les réaliseront.

**Risque.** Définir un rôle comme la simple étiquette déjà portée par
l'occurrence.

### Phase 4 — Définir l'accord exact

**Question.** Quelle égalité ou quelle correspondance garantit qu'une occurrence
réalise réellement un rôle ?

**Sortie.** Une structure d'accord assez fine pour dériver les projections
pertinentes.

**Risque.** Accumuler des accords partiels sans noyau commun, ou demander une
égalité plus forte que ce que l'usage exige.

### Phase 5 — Séparer couverture, injectivité et exhaustivité

**Question.** Chaque rôle possède-t-il un témoin ? Deux rôles distincts
possèdent-ils des témoins distincts ? Toute occurrence doit-elle être classée ?

**Sortie.** Trois décisions explicites, au lieu d'une notion ambiguë de
« réalisation complète ».

**Risque.** Interdire les continuations en confondant couverture et exhaustivité.

### Phase 6 — Identifier les propriétés candidates

**Question.** L'ordre, l'adjacence, la participation ou la contiguïté doivent-ils
être primitifs ?

**Sortie.** Une liste de dépendances à tester.

**Risque.** Ajouter comme champs toutes les propriétés désirées avant d'étudier
leurs relations.

### Phase 7 — Construire un carrier affaibli

**Question.** Quelle structure peut être retirée tout en conservant les notions
déjà établies ?

**Sortie.** Un modèle expérimental où les implications candidates deviennent
réellement testables.

**Risque.** Choisir un carrier encore trop contraint, dans lequel le
contre-modèle recherché est exclu par construction.

### Phase 8 — Produire des modèles séparateurs

**Question.** Peut-on conserver les couches faibles tout en violant la propriété
candidate ?

**Sortie.** Un contre-modèle typé ou une preuve que la séparation considérée est
impossible sous les hypothèses retenues.

**Risque.** Utiliser un exemple qui détruit également une hypothèse que l'on
prétendait conserver.

### Phase 9 — Réintroduire la composition réelle

**Question.** Quelles propriétés deviennent dérivables sur le carrier complet ?

**Sortie.** Des théorèmes de reconstruction et une liste minimale de primitives.

**Risque.** Conserver simultanément comme primitive une propriété et la structure
qui la rend déjà dérivable.

### Phase 10 — Définir le transport fidèle

**Question.** Quelles occurrences et quels accords doivent survivre au changement
de représentation ?

**Sortie.** Des applications aller-retour et des accords structuraux pour les
occurrences transportées.

**Risque.** Certifier seulement l'état final ou une égalité de cardinalités.

### Phase 11 — Extraire les invariants

**Question.** Quelles valeurs numériques ou classifications sont déterminées par
la structure conservée ?

**Sortie.** Des invariants dérivés accompagnés de leur dépendance structurelle.

**Risque.** Utiliser l'invariant numérique pour redéfinir rétroactivement la
structure.

### Phase 12 — Définir séparément norme et régime

**Question.** Quelle propriété indépendante exprime ce qui doit être satisfait,
et quel mécanisme opérationnel décide l'admission ?

**Sortie.** Deux familles de types distinctes sur le même carrier.

**Risque.** Définir la norme par le régime et rendre l'adéquation tautologique.

### Phase 13 — Prouver soundness et complétude

**Question.** Le régime est-il exact relativement à la norme ?

**Sortie.** Des transformations dans les deux directions, éventuellement
accompagnées d'une classification du carrier canonique.

**Risque.** Confondre l'équivalence extensionnelle des carriers avec l'égalité
des structures de témoins.

### Phase 14 — Construire une sortie minimale

**Question.** Existe-t-il un premier candidat qui conserve construction et
fidélité tout en quittant le régime ou la norme ?

**Sortie.** Un objet concret avec témoins positifs et réfutations négatives.

**Risque.** Choisir un candidat qui échoue déjà à être construit ou fidèlement
réalisé.

### Phase 15 — Produire le diagnostic

**Question.** Quelle propriété exacte est perdue et lesquelles restent
conservées ?

**Sortie.** Une structure typée réunissant le candidat, ses fidélités, son rejet,
l'adéquation pertinente et, si possible, une réfutation normative directe.

**Risque.** Réduire le diagnostic à un booléen ou à une négation sans conserver
les témoins positifs.

### Vue condensée

```text
présentation
  ↓
occurrences individuées
  ↓
rôles + accord exact + injectivité
  ↓
carriers affaiblis + modèles séparateurs
  ↓
primitives minimales + propriétés reconstruites
  ↓
transport fidèle + invariants
  ↓
norme indépendante ⇄ régime
  ↓
sortie minimale conservant ses témoins positifs
  ↓
diagnostic de la rupture exacte
```

## 16. Critères d'échec et contrôles d'audit

Une application de la méthode doit être rejetée ou révisée lorsqu'un des
problèmes suivants apparaît.

### 16.1 Individuation circulaire

Les occurrences sont définies par la valeur que l'interprétation doit produire.
Le transport ne peut alors plus montrer qu'il préserve leur identité : cette
identité dépend déjà du transport.

### 16.2 Rôle purement nominal

Le rôle se réduit à une étiquette sans accord sur les données constitutives. La
preuve certifie une classification déclarée, non la réalisation d'une exigence.

### 16.3 Couverture prétendument exhaustive

Une fonction des exigences vers les occurrences est présentée comme une
bijection sans inverse ni preuve de surjectivité. Toute conclusion excluant des
occurrences supplémentaires devient alors injustifiée.

### 16.4 Carrier séparateur inadéquat

Le carrier faible détruit l'exactitude locale qu'il devait conserver, ou garde
implicitement la composabilité qu'il devait retirer. Le contre-modèle ne sépare
plus les propriétés annoncées.

### 16.5 Participation réduite à la position

La présence d'un indice entre deux autres est utilisée comme preuve
d'appartenance à leur composition. Les contraintes de source, de cible et de
génération sont absentes.

### 16.6 Fidélité réduite à la sortie finale

Deux réalisations sont déclarées équivalentes parce qu'elles ont le même état
terminal ou le même nombre d'étapes. Les occurrences, leurs accords ou leur
ordre peuvent pourtant avoir été modifiés.

### 16.7 Norme définie par le régime

La spécification contient directement la preuve d'admission ou est définie comme
l'image du classificateur opérationnel. La soundness ne fournit alors plus de
contrôle indépendant.

### 16.8 Diagnostic sans information positive

La sortie est uniquement représentée par `¬ Regime candidate`. Rien n'atteste
que le candidat est constructible, qu'il conserve les exigences locales ou qu'il
reste fidèlement interprétable.

### 16.9 Généralisation sans quantificateurs

Un résultat valable pour toute implémentation satisfaisant une interface est
reformulé comme un résultat valable pour toute implémentation. La condition
d'interface doit rester visible.

### 16.10 Confusion des statuts documentaires

Une extraction méthodologique ou une généralisation proposée est présentée
comme un théorème Lean. Chaque affirmation importante doit pouvoir être reliée à
son statut et, lorsqu'elle est formelle, à une déclaration précise.

## 17. Portée après les Cycles 1 et 2

### 17.1 Ce que le cycle 1 établit effectivement

Le cycle 1 fournit une instance formelle dans laquelle :

- les occurrences sont dépendamment typées et restent individuées ;
- les exigences non fermantes possèdent une réalisation exacte et injective ;
- l'ordre et l'adjacence sont séparés sur un carrier faible puis reconstruits
  dans les histoires réelles ;
- la position intermédiaire est distinguée de la participation constitutive ;
- les occurrences libres et concrètes sont reliées par des correspondances
  inverses avec accord structurel ;
- une norme autonome et un régime opérationnel sont adéquats dans les deux
  directions ;
- une continuation minimale reste exactement réalisable dans toute algèbre
  fournie tout en échouant à la norme et au régime ;
- la rupture est localisée sans suppression de la construction.

### 17.2 Ce que le Cycle 2 ajoute — et n'ajoute pas

Le Cycle 2 observe le régime et la norme du Cycle 1 par `Nonempty`, transporte
leur équivalence propositionnelle à travers la représentation exacte et combine
cette exactitude déterminée avec un statut diagonal hors de la clôture réflexive
globale. Cela confirme que la discipline méthodologique de conservation avant
projection reste pertinente au niveau réflexif.

Le Cycle 2 n'est toutefois pas une seconde instance non périmétrale de la
méthode. Il réemploie l'adéquation du Cycle 1 et ajoute une couche de
représentation ; il ne fournit pas un nouveau domaine muni de rôles constitutifs
relationnels reconstruits indépendamment.

### 17.3 Ce que le développement actuel n'établit pas encore

Il ne démontre pas :

- que tout problème d'alignement possède naturellement des rôles constitutifs
  relationnels ;
- que la méthode est complète pour découvrir toutes les dépendances primitives ;
- que toute norme pertinente peut être exprimée sur le carrier actuel ;
- que l'interface normative est polymorphe sur un carrier arbitraire ;
- que l'OOD structurel constitue déjà une théorie formalisée générale ;
- que les conclusions sur l'instance circulaire s'appliquent directement aux
  systèmes d'apprentissage contemporains.

Ces limites ne réduisent pas le résultat démontré. Elles définissent le travail
nécessaire pour transformer l'extraction méthodologique en théorie plus générale.

### 17.4 Étapes formelles futures

Un programme naturel comprendrait :

1. isoler une structure Lean générique de rôle constitutif relationnel ;
2. paramétrer l'interface normative sur un carrier arbitraire muni d'un type
   d'occurrences ;
3. formaliser une notion de morphisme préservant les rôles et leurs accords ;
4. exprimer les modèles séparateurs dans une interface générique de réduction de
   structure ;
5. définir un schéma typé d'OOD structurel distinguant construction, régime et
   norme ;
6. instancier le cadre dans au moins un second domaine non périmétral ;
7. comparer les primitives retenues et les théorèmes reconstruits entre les deux
   instances.

Une seconde instance est particulièrement importante. Elle permettrait de
séparer ce qui appartient réellement à la méthode de ce qui dépend de la
géométrie circulaire du premier cas.

## 18. Carte des ancrages Lean

| Fonction méthodologique | Déclaration principale |
|---|---|
| occurrence individuée dans une histoire | `History.Occurrence` |
| accord exact entre exigence et occurrence | `RequirementOccurrenceAgreement` |
| couverture exacte et injective | `ExactNonClosingRealization` |
| carrier expérimental affaibli | `SemanticTrace` |
| couverture exacte sur le carrier faible | `SemanticExactNonClosingRealization` |
| ordre explicite sur le carrier faible | `SemanticOrderPreserved` |
| contre-modèle de permutation | `permutedExample_not_order_preserved` |
| position intermédiaire | `SemanticTrace.Between` |
| participation exacte à un pont | `ExactSemanticBridgeSegment` |
| pont constitutif effectif | `EffectiveConstitutiveBridge` |
| contre-modèles d'intercalation | `interleavedExample_no_effective_bridge_p1_p2`, `interleavedExample_no_effective_bridge_p2_p3` |
| précédence reconstruite | `ExactNonClosingRealization.preservesPrecedence` |
| adjacence reconstruite | `ExactNonClosingRealization.preservesNext` |
| unicité résiduelle abstraite | `positiveExtension_hasUniqueResidualOccurrence` |
| continuation d'une occurrence | `positiveContinuation_exactlyOne` |
| accord d'occurrence concret | `ConcreteOccurrenceAgreement` |
| interprétation exacte d'une histoire | `ExactHistoryInterpretation` |
| construction de l'interprétation exacte | `exactlyInterpretHistory` |
| additivité de la longueur | `History.length_append` |
| égalité de longueur dérivée du régime | `samePerimeter_length_eq` |
| classification exacte d'un régime | `ExactRegimeClassification` |
| sortie typée | `RegimeExit` |
| sortie uniforme | `UniformRegimeExit` |
| norme circulaire indépendante | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| complétude du carrier normatif | `CircularSpecificationSatisfaction.eq_perimeter` |
| complétude du régime | `circularSpecification_complete` |
| interface d'adéquation | `NormativeAdequacy`, `AdequateAlong` |
| sortie relative à une spécification | `SpecRelativeHistoryExit` |
| témoin canonique | `oneStepAfterPerimeter` |
| sortie uniforme canonique | `oneStepUniformPerimetralRegimeExit` |
| diagnostic relatif canonique | `oneStepSpecRelativeHistoryExit` |
| réfutation normative directe | `oneStepSpecRelativeHistoryExit_notSpecification` |

## 19. Reproduction et audit

Les résultats Lean cités sont répartis dans :

- [`SegmentedResidualRole.lean`](../../SegmentedResidualRole.lean) ;
- [`AbstractSegmentedTurning.lean`](../../AbstractSegmentedTurning.lean) ;
- [`StrongPerimetralTurning.lean`](../../StrongPerimetralTurning.lean).

Après installation d'`elan`, ou d'un environnement équivalent capable de lire
`lean-toolchain`, compiler le projet avec :

```bash
lake build
```

Depuis la racine du dépôt, le manifeste d'intégrité peut être vérifié sous Linux
ou macOS avec :

```bash
bash scripts/verify-manifest.sh
```

Sous Windows PowerShell :

```powershell
powershell -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

L'audit d'une adaptation future devrait en outre vérifier :

1. que les occurrences ne sont pas définies par leurs lectures ;
2. que chaque accord annoncé apparaît dans un type ou un théorème identifiable ;
3. que les modèles séparateurs conservent réellement les couches faibles ;
4. que les propriétés dites dérivées sont accompagnées de leur reconstruction ;
5. que les interprétations fournissent des lois d'aller-retour ;
6. que la norme ne dépend pas définitionnellement du régime évalué ;
7. que chaque sortie conserve un témoin positif de fidélité ;
8. que les quantificateurs sur les implémentations restent explicites ;
9. que les propositions conceptuelles sont distinguées des résultats Lean.

## 20. Conclusion

La méthode des rôles constitutifs relationnels organise une formalisation autour
de ce qui doit être préservé avant toute réduction : les occurrences, leurs
formations et les relations qui déterminent leur participation à une
construction.

Son geste central n'est pas d'ajouter toujours plus de primitives. Il consiste à
tester les dépendances : affaiblir le carrier, construire un modèle séparateur,
réintroduire la structure et observer ce qui devient dérivable. Cette démarche
permet de réduire les primitives sans réduire prématurément les objets.

Le transport fidèle prolonge cette discipline entre représentations. Une
implémentation n'est pas certifiée par la seule égalité de sa sortie finale, mais
par la conservation exacte des occurrences et des accords pertinents. Les
invariants numériques peuvent alors être lus comme les conséquences d'une
structure déjà préservée.

Dans l'analyse normative, la même méthode impose de séparer ce qui peut être
construit, ce qui peut être fidèlement réalisé, ce qu'un régime admet et ce
qu'une norme indépendante exige. L'adéquation entre régime et norme devient un
théorème à établir, non une identité postulée. Une sortie peut alors conserver
son existence et sa fidélité tout en portant la preuve exacte de sa rupture
normative.

La formulation condensée de la méthode est donc :

> **Préserver l'individuation la plus fine et les relations qui la constituent ;
> éprouver chaque dépendance sur le carrier minimal où elle peut être séparée ;
> ne transporter, classifier ou mesurer qu'après avoir démontré ce qui est
> conservé ; puis diagnostiquer une rupture en maintenant sur le même objet les
> témoins positifs de ce qui subsiste et la preuve négative de ce qui cesse
> d'être satisfait.**

Le Cycle 1 vérifie une instance complète de cette méthode. Le Cycle 2 transporte
l'un de ses résultats d'adéquation vers une couche réflexive de représentation,
mais ne constitue pas une seconde instance de domaine. La généralisation de la
méthode demande donc encore de formaliser l'interface méthodologique elle-même et
de l'éprouver sur d'autres domaines, sans effacer la distinction entre résultat
Lean, conséquence dérivée et proposition théorique.
