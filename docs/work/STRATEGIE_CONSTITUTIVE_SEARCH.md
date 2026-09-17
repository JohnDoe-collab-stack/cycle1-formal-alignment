# Stratégie complète - recherche constitutive et calcul par trajectoire

## Statut du document

Ce document est un document de chantier de la branche `research/constitutive-search`.

Il fixe la stratégie scientifique et formelle du travail en cours autour de l'idée suivante :

> le chemin de résolution n'est pas parcouru par le calcul comme une structure déjà donnée. Le chemin est constitué par le calcul lui-même. Les déterminations déjà obtenues deviennent une partie de la structure utilisée pour produire les déterminations suivantes.

Ce document n'est pas une revendication sur `P = NP` et ne doit pas être fusionné dans `main` sous cette forme. Conformément aux règles du dépôt, il devra être supprimé ou transformé en documentation scientifique canonique avant une éventuelle pull request vers `main`.

---

## 1. But scientifique

Le programme vise à formaliser une classe de calculs où une recherche se construit par interaction entre :

```text
possibilités de continuation
        ↓
contraintes déjà constituées
        ↓
relations calculables localement
        ↓
transports entre espaces de continuation
        ↓
réduction de la frontière active
        ↓
nouvelles déterminations
        ↓
nouveau contexte de calcul
```

L'objectif n'est pas de supposer une procédure qui sait quelle branche contient une solution.

L'objectif est de déterminer si des relations structurelles plus faibles peuvent permettre de construire positivement des transformations de continuations suffisantes pour réduire la recherche sans décider directement l'existence d'une solution dans chaque branche.

Le cas d'étude final visé est SAT, mais aucune primitive du noyau générique ne doit mentionner SAT, P, NP, satisfaisabilité ou complexité polynomialement bornée.

La complexité intervient seulement après que la structure de calcul, ses transformations et ses invariants de correction ont été reconstruits.

---

## 2. Principe méthodologique

Le travail suit la discipline générale du projet :

```text
affaiblir
→ séparer
→ reconstruire
```

Aucune propriété forte ne doit être ajoutée parce qu'elle rendrait la preuve facile.

En particulier, il est interdit de mettre comme primitive une propriété du type :

```text
la branche conservée contient une solution si une solution existe
```

ou :

```text
la branche A est satisfaisable implique que la branche B est satisfaisable
```

lorsque cette propriété peut être remplacée par une construction positive plus fondamentale.

La forme primitive recherchée est plutôt :

```text
Completion A → Completion B
```

Une implication d'existence doit ensuite être dérivée de cette transformation.

L'ordre de dépendance prévu est :

```text
états constitués
→ espaces de complétions
→ splits de continuation
→ transports directionnels
→ réduction de frontière
→ reconstruction relationnelle des transports
→ contexte dynamique et ancres
→ largeur constitutive
→ terminaison structurelle
→ bornes de représentation
→ bornes de temps
→ instance SAT
```

La mesure numérique ne doit pas constituer rétroactivement la structure.

---

## 3. Invariants conceptuels à préserver

Les distinctions suivantes sont obligatoires pendant tout le chantier :

```text
état de recherche ≠ lecture de l'état
branche ≠ existence d'une solution dans la branche
relation structurelle ≠ transport de complétions
transport de complétions ≠ transport exact d'identités
existence d'un transport ≠ recherche réussie d'un transport
échec de recherche ≠ preuve de non-existence
séparation des profils ≠ existence d'un correspondant
unicité d'un correspondant ≠ existence d'un correspondant
réduction locale ≠ réduction globale garantie
frontière petite ≠ représentation petite
terminaison structurelle ≠ temps polynomial
équivalence sémantique ≠ identité constitutive
```

Une couche ultérieure ne doit jamais être utilisée silencieusement pour définir une couche antérieure.

---

## 4. Noyau déjà engagé sur la branche

### 4.1 `ConstitutiveSearch.ContinuationTransport`

Ce module définit le noyau directionnel minimal.

Pour un type d'états `State` et une famille :

```lean
Completion : State → Type
```

un transport de continuation est une donnée positive :

```lean
ContinuationTransport Completion source target
```

qui contient essentiellement :

```text
Completion source → Completion target
```

Aucune injectivité, aucun inverse et aucune décidabilité ne sont supposés.

Le module contient aussi un split binaire exact :

```text
Completion parent
    ≃
Completion left ⊕ Completion right
```

et les constructions qui permettent d'absorber une branche dans l'autre lorsqu'un transport directionnel existe.

Ce niveau est volontairement indépendant de toute notion de complexité.

### 4.2 `ConstitutiveSearch.FrontierReduction`

Cette couche introduit une frontière active de recherche.

Le rôle de la frontière est de représenter les histoires ou états qui restent simultanément nécessaires faute de transport permettant encore de les absorber.

Une réduction doit conserver constructivement toute complétion pertinente en fournissant un chemin explicite vers un état retenu.

Le but n'est pas de conserver une simple propriété existentielle, mais une transformation positive suffisamment forte pour dériver cette propriété.

### 4.3 `ConstitutiveSearch.RelationalTransport`

Cette couche sépare trois objets :

```text
relation structurelle
        ↓
action démontrée sur les complétions
        ↓
transport de continuation
```

La recherche exécutable d'un témoin relationnel reste distincte de la preuve de son inexistence.

Un résultat `none` signifie seulement qu'aucun témoin n'a été trouvé par la procédure considérée.

Il ne doit jamais être transformé sans théorème supplémentaire en certificat d'impossibilité.

---

## 5. Objet central à construire : la frontière constitutive

Pour une instance donnée, le calcul maintient une frontière :

```text
F₀
→ F₁
→ F₂
→ ...
```

Chaque élément de `Fₖ` est une histoire constituée, pas seulement une formule résiduelle ou une valeur.

Chaque étape comporte conceptuellement deux mouvements.

### Expansion

Un état peut produire plusieurs continuations :

```text
H
↓
H₁ OR H₂ OR ... OR Hₙ
```

L'expansion doit être structurellement exacte relativement à la notion de complétion choisie.

### Réduction

Si l'on construit :

```text
Completion Hᵢ → Completion Hⱼ
```

alors `Hᵢ` devient absorbable par `Hⱼ` relativement à la conservation d'existence de complétion.

La réduction ne dépend pas du fait de savoir si `Hᵢ` est effectivement positif.

La frontière réduite contient les états qui ne sont pas encore absorbables par les transports actuellement reconstructibles.

---

## 6. Largeur constitutive

La notion quantitative centrale sera introduite seulement après la définition de la frontière et de sa réduction.

Intuition :

> la largeur constitutive à une étape mesure le nombre d'états de frontière qui restent simultanément nécessaires après toutes les réductions justifiées par l'interface de transports disponible.

Cette largeur ne doit pas être confondue avec :

```text
nombre de solutions
nombre de témoins
nombre de branches syntaxiques produites avant réduction
largeur d'un arbre de recherche brut
```

Le programme devra distinguer au moins trois régimes :

```text
largeur 1
largeur polynomialement contrôlée
largeur non contrôlée ou explosive
```

Le cas de largeur 1 correspond à une trajectoire effectivement orientée vers un représentant unique à chaque étape.

Le cas de largeur polynomialement contrôlée autorise plusieurs histoires incomparables sans exiger un ordre total.

Le dernier cas doit être conservé comme diagnostic d'échec du mécanisme disponible, pas remplacé par une conclusion arbitraire.

---

## 7. Reconstruction des transports depuis des relations locales

Le coeur scientifique du programme se situe ici.

Il faut éviter une structure primitive du type :

```lean
transport : Completion A → Completion B
```

lorsqu'une instance concrète doit montrer d'où ce transport provient.

La branche générique doit autoriser cette interface abstraite, mais les instances scientifiques devront reconstruire le transport depuis une structure relationnelle plus faible.

Schéma cible :

```text
relations locales entre états
        ↓
observations structurées
        ↓
profil relationnel
        ↓
condition de transformation
        ↓
action sur une complétion
        ↓
ContinuationTransport
```

Il faut distinguer soigneusement :

```text
le profil permet de distinguer les états
```

et :

```text
le profil permet de transformer les complétions
```

La seconde propriété est plus forte et devra être démontrée séparément.

---

## 8. Ancres dynamiques

Le projet d'alignement utilise déjà des relations à des ancres pour reconstruire des correspondances.

La recherche constitutive doit tester une version dynamique de cette idée.

Une histoire `Hₖ` contient des déterminations déjà constituées :

```text
Aₖ = {a₁, a₂, ..., aₖ}
```

Ces déterminations peuvent devenir des points de référence pour observer les continuations suivantes.

Une continuation `C` peut recevoir un profil :

```text
R(a₁, C)
R(a₂, C)
...
R(aₖ, C)
```

Le point décisif est que :

```text
Aₖ
→ nouvelles observations
→ nouvelle détermination
→ Aₖ₊₁
```

Le chemin construit donc progressivement une partie du système de référence utilisé pour calculer le chemin suivant.

C'est la formulation exacte de l'idée :

> le chemin est le calcul lui-même.

La nouvelle détermination n'est pas seulement un résultat intermédiaire. Elle modifie l'espace relationnel dans lequel l'étape suivante est calculée.

---

## 9. Composition des transports

Les transports doivent être composables.

Si :

```text
Completion A → Completion B
```

et :

```text
Completion B → Completion C
```

alors on doit construire :

```text
Completion A → Completion C
```

Cette composition permet de ne pas conserver chaque réduction intermédiaire comme branche active.

La provenance de la réduction doit néanmoins rester reconstructible.

Une phase ultérieure pourra introduire une structure de DAG de réduction où un état supprimé conserve un chemin de transport vers son représentant actif.

Les propriétés à établir comprennent :

```text
composition des transports
identité
cohérence des réductions composées
indépendance vis-à-vis d'intermédiaires lorsqu'elle est justifiée
```

Aucune unicité globale du transport ne doit être supposée sans structure supplémentaire.

---

## 10. Canonicalité et ambiguïté

Plusieurs transports peuvent exister entre les mêmes espaces de complétions.

Le chantier doit distinguer :

```text
existence d'un transport
unicité de son action
choix canonique d'un transport
```

Un transport quelconque peut suffire pour préserver l'existence d'une solution.

Une théorie de persistance ou de reconstruction plus forte peut nécessiter davantage.

Il ne faut pas importer automatiquement les exigences d'`ExactTypeTransport` dans ce noyau.

L'un des objectifs de la branche est précisément de déterminer le minimum réellement nécessaire pour la réduction de recherche.

---

## 11. Séparateurs obligatoires

Chaque propriété forte candidate doit être testée par un séparateur.

### 11.1 Transport directionnel sans inverse

Construire une instance où :

```text
Completion A → Completion B
```

existe mais où :

```text
Completion B → Completion A
```

est impossible.

Ce séparateur existe déjà dans les régressions initiales et doit rester présent.

### 11.2 Transport non injectif

Montrer qu'un transport suffisant pour préserver l'existence peut fusionner plusieurs complétions.

Cela empêche d'introduire inutilement l'injectivité comme primitive du noyau.

### 11.3 Distinction sans dominance

Construire des profils qui séparent parfaitement deux états mais ne fournissent aucun transport entre leurs complétions.

Conclusion attendue :

```text
séparation
n'implique pas
réduction de frontière
```

### 11.4 Dominance sémantique sans reconstruction exécutable

Construire une situation où un transport existe mathématiquement mais où l'interface de recherche choisie ne sait pas le reconstruire.

Conclusion attendue :

```text
existence du transport
n'implique pas
transport calculé par l'interface
```

### 11.5 Réduction locale sans borne globale

Construire une famille où plusieurs réductions locales sont possibles mais où la largeur de frontière continue de croître rapidement.

Conclusion attendue :

```text
réduction locale
n'implique pas
largeur globalement contrôlée
```

### 11.6 Frontière petite avec représentations grandes

Construire ou formaliser un modèle où le nombre d'états actifs est faible mais où leur représentation ou les certificats de transport peuvent devenir très grands.

Conclusion attendue :

```text
petite largeur
n'implique pas
petit coût de représentation
```

### 11.7 Progression sans terminaison bornée

Construire un modèle où chaque étape est différente de la précédente mais où aucune borne structurale suffisante n'est disponible.

Conclusion attendue :

```text
irréflexivité locale
n'implique pas
borne polynomialement contrôlée
```

---

## 12. Modèle générique de calcul à construire

Après les noyaux de transport et de frontière, introduire une structure de calcul générique.

Esquisse conceptuelle :

```lean
structure ConstitutiveSearchSystem where
  State : Type
  Completion : State → Type
  expand : State → ...
  relation : State → State → Type
  relationTransport : relation a b → ContinuationTransport Completion a b
```

Cette esquisse ne fixe pas encore la représentation de la frontière ni les conditions de finitude.

Une seconde interface exécutable pourra ajouter :

```text
énumération finie des successeurs immédiats
procédure de recherche de relations
procédure de réduction
états terminaux
vérification terminale
```

La version propositionnelle et la version exécutable doivent rester séparées.

---

## 13. Théorème générique de correction de trajectoire

Premier objectif global : établir sans complexité que la trajectoire de frontières conserve exactement la possibilité d'une complétion pertinente.

Forme visée :

```text
completion initiale
        ↓
expansion exacte
        ↓
réductions par transports
        ↓
frontière suivante
```

avec un théorème constructif du type :

```text
Completion initial
→ FrontierCompletion frontier_k
```

pour toute étape construite.

Si la réciproque est nécessaire pour une instance, elle devra être prouvée séparément.

Le noyau de décision positive n'a pas besoin d'une équivalence lorsque la direction de conservation suffit.

---

## 14. Terminaison structurelle avant complexité

La terminaison ne doit pas être définie d'abord par un compteur arbitraire.

Il faut rechercher une relation structurelle de progrès.

Exemples possibles selon l'instance :

```text
nouvelle variable constituée
nouvelle contrainte irréversible ajoutée
réduction stricte d'un espace de choix
progression dans une profondeur de genèse
réduction d'une frontière selon une mesure dérivée
```

On doit d'abord prouver que les transitions légales progressent relativement à cette structure.

Une longueur ou une borne numérique pourra ensuite être dérivée.

Cette discipline suit directement la méthode générale du dépôt.

---

## 15. Couche de complexité

La complexité ne sera introduite qu'après la correction structurelle.

Le théorème générique visé devra séparer au moins quatre bornes.

### 15.1 Profondeur

Nombre maximal d'étapes constitutives nécessaires avant un état terminal.

### 15.2 Largeur

Nombre maximal d'états irréductibles simultanément présents dans une frontière réduite.

### 15.3 Taille de représentation

Taille maximale de chaque état, de son contexte dynamique et des témoins relationnels nécessaires à sa réduction.

### 15.4 Coût local

Coût maximal de :

```text
l'expansion d'un état
la recherche d'un témoin relationnel
la construction du transport associé
la réduction d'une frontière
la vérification terminale
```

Un résultat polynomial devra démontrer les quatre composantes.

Une simple borne de largeur ne suffira pas.

---

## 16. Théorème de largeur polynomialement contrôlée

Une fois les couches précédentes établies, viser un théorème conditionnel honnête :

> si une famille de systèmes de recherche possède une profondeur polynomialement bornée, une largeur constitutive polynomialement bornée, des représentations polynomialement bornées et des opérations locales polynomialement exécutables, alors la procédure de frontière correspondante est polynomialement exécutable.

Ce théorème ne résout aucun problème difficile à lui seul.

Il localise exactement ce qu'une instance SAT devra établir.

---

## 17. Instance SAT

SAT ne doit être introduit qu'après stabilisation du noyau générique.

### 17.1 État SAT

Un état doit conserver au minimum :

```text
formule ou représentation résiduelle
assignations déjà constituées
provenance des assignations
transformations appliquées
contexte relationnel utile
```

Deux états ayant la même formule résiduelle ne doivent pas nécessairement être identifiés sans preuve que la provenance peut être oubliée pour la propriété étudiée.

### 17.2 Complétion SAT

Une complétion d'un état est une affectation des variables restantes qui prolonge les déterminations déjà constituées et satisfait la formule initiale relativement à cette histoire.

La définition doit permettre de reconstruire un témoin final pour l'instance initiale.

### 17.3 Split SAT

Le split sur une variable doit construire une décomposition exacte de l'espace de complétions :

```text
Completion H
≃
Completion (H + x := false)
⊕
Completion (H + x := true)
```

La preuve doit porter sur les complétions, pas seulement sur une équivalence propositionnelle de satisfaisabilité.

### 17.4 Vérification terminale

Lorsque toutes les déterminations nécessaires sont constituées, le témoin terminal doit être vérifiable directement.

Aucune décision SAT générale ne doit être utilisée dans les étapes intermédiaires.

---

## 18. Générateurs de transports SAT à tester

Commencer par des transformations dont l'action sur une affectation est explicite.

### 18.1 Affaiblissement de contraintes

Si une branche possède toutes les contraintes d'une autre et éventuellement davantage, une affectation satisfaisant la branche plus forte peut être transportée vers la branche plus faible.

Le transport peut souvent être l'identité sur l'affectation restante.

### 18.2 Renommage de variables

Une bijection ou injection structurée sur les variables peut transporter les affectations lorsque la transformation des clauses est prouvée compatible.

Le but est de reconstruire l'action sur les complétions depuis le renommage lui-même.

### 18.3 Symétries

Tester des symétries syntaxiques explicites de la formule et leur action sur les complétions.

### 18.4 Substitutions locales

Certaines substitutions peuvent induire un transport directionnel même lorsqu'elles ne sont pas inversibles.

### 18.5 Propagation de contraintes

Étudier séparément les transformations produites par propagation unitaire, simplification et élimination locale.

Il faut distinguer :

```text
simplification équivalente
```

et :

```text
simplification seulement directionnelle relativement aux complétions
```

### 18.6 Composition

Les transformations élémentaires doivent composer pour reconstruire des transports plus riches sans introduire un solveur global.

---

## 19. Test de familles positives

Avant SAT général, valider le modèle sur des familles où l'on s'attend à une structure fortement réductible.

Exemples possibles :

```text
2-SAT
Horn-SAT
formules avec forte symétrie
familles à largeur structurelle déjà contrôlée
CSP où la cohérence locale suffit
```

Le but n'est pas de redémontrer leur appartenance à P de manière artificielle.

Le but est de vérifier que la notion de frontière constitutive capture effectivement une raison structurelle de leur tractabilité.

Si le formalisme ne sait pas expliquer au moins certaines classes déjà tractables sans tricher, il est trop faible ou mal posé.

---

## 20. Test de familles séparatrices

Il faut également rechercher des familles où chaque interface faible échoue.

Exemples de questions :

```text
l'affaiblissement seul laisse-t-il une largeur exponentielle ?
les renommages seuls suffisent-ils à fusionner les symétries utiles ?
la propagation locale produit-elle une frontière non contrôlée ?
la composition des transports réduit-elle réellement la largeur ?
les ancres dynamiques créent-elles des relations nouvelles ou seulement des labels ?
```

Chaque échec doit devenir un résultat du chantier, pas être masqué.

---

## 21. Critères anti-triche

Toute instance prétendant obtenir une réduction forte devra passer les contrôles suivants.

### Gate A - aucune décision cachée de satisfaisabilité

Aucune fonction utilisée pour construire un transport ne doit appeler ou supposer :

```text
SAT(branch)
UNSAT(branch)
existence d'un témoin
absence de témoin
```

sauf dans les théorèmes de spécification utilisés uniquement pour prouver la correction d'une procédure déjà définie indépendamment.

### Gate B - témoins positifs

Lorsqu'une branche est absorbée, la justification doit contenir une transformation effective de complétions ou une construction dont cette transformation est dérivée.

### Gate C - échec de recherche honnête

`none` ne devient jamais une réfutation sans théorème de complétude explicite de la procédure de recherche.

### Gate D - pas de classicalisation silencieuse

Respecter les règles du dépôt : aucune dépendance à `Classical`, aucune déclaration `noncomputable`, aucun `sorry`, aucun axiome ajouté.

### Gate E - représentation contrôlée

Une preuve de largeur polynomialement bornée est insuffisante si les états, ancres ou certificats deviennent exponentiellement grands.

### Gate F - profondeur contrôlée

Une étape strictement progressive n'est pas suffisante si le nombre d'étapes peut être superpolynomial.

### Gate G - généralité réelle de SAT

Une conclusion sur SAT général exige que l'instance traite toutes les CNF de la classe annoncée sans hypothèse cachée de structure favorable.

### Gate H - séparation décision / construction

La vérification finale d'un témoin ne doit pas être utilisée rétroactivement pour guider la construction du témoin.

---

## 22. Plan de modules Lean

Architecture proposée à court et moyen terme :

```text
ConstitutiveSearch/
  ContinuationTransport.lean          [créé]
  FrontierReduction.lean              [créé]
  RelationalTransport.lean            [créé]
  DynamicAnchors.lean
  FrontierHistory.lean
  StructuralProgress.lean
  ConstitutiveWidth.lean
  ExecutableReduction.lean
  ComplexityInterface.lean

ConstitutiveSearch/SAT/
  Syntax.lean
  State.lean
  Completion.lean
  BinarySplit.lean
  WeakeningTransport.lean
  RenamingTransport.lean
  SubstitutionTransport.lean
  PropagationTransport.lean
  RelationalReduction.lean
  Frontier.lean
  WidthExperiments.lean

Tests/
  ConstitutiveSearchRegression.lean    [créé]
  ConstitutiveFrontierRegression.lean  [créé]
  RelationalTransportRegression.lean   [créé]
  DynamicAnchorsRegression.lean
  ConstitutiveWidthRegression.lean
  SATTransportRegression.lean
  SATSeparatorsRegression.lean
```

Les noms peuvent évoluer si l'architecture réelle impose une meilleure factorisation.

---

## 23. Plan de développement par phases

### Phase 0 - noyau directionnel

Statut : engagé.

Livrables :

```text
ContinuationTransport
composition
préservation d'existence dérivée
ExactBinarySplit
absorption gauche / droite
séparateurs directionnels
```

Gate : compilation, audits axiomatiques, régressions.

### Phase 1 - frontière proof-relevant

Statut : engagé.

Livrables :

```text
frontière active
expansion structurée
absorption interne
conservation des complétions
provenance des réductions
```

Gate : aucune branche supprimée sans transport positif.

### Phase 2 - reconstruction relationnelle

Statut : engagé.

Livrables :

```text
relation locale
interprétation de relation en transport
classification directionnelle
recherche exécutable sans fausse complétude
```

Gate : `none` reste distinct de l'impossibilité.

### Phase 3 - ancres dynamiques

Statut : à construire.

Livrables :

```text
contexte d'ancres constitué par l'histoire
extension canonique du contexte
profils relatifs au contexte courant
reconstruction de relations supplémentaires
```

Gate : démontrer qu'une nouvelle ancre peut ajouter une distinction ou un transport réellement nouveau dans au moins une instance non triviale.

### Phase 4 - histoire de frontière

Statut : à construire.

Livrables :

```text
suite proof-relevant de frontières
provenance de chaque état actif
DAG de réductions
composition des transports vers les représentants courants
```

Gate : reconstruire explicitement comment une complétion initiale atteint un état actif ultérieur.

### Phase 5 - progression structurelle

Statut : à construire.

Livrables :

```text
relation de progrès
irréflexivité ou bien-fondation adaptée
conditions de terminalité
```

Gate : aucun compteur numérique ne doit servir de définition cachée du progrès si une relation constitutive plus primitive est visée.

### Phase 6 - largeur constitutive

Statut : à construire.

Livrables :

```text
frontière irréductible relative à une interface
notion de largeur
monotonies ou bornes utiles
séparateurs largeur / taille
```

Gate : distinguer cardinalité de frontière, taille de représentation et coût de réduction.

### Phase 7 - interface de complexité

Statut : à construire après les phases structurelles.

Livrables :

```text
coût local explicite
borne de profondeur
borne de largeur
borne de taille
théorème conditionnel de temps polynomial
```

Gate : aucune hypothèse de complexité ne doit être cachée dans une primitive de transport.

### Phase 8 - instance SAT minimale

Statut : à construire.

Livrables :

```text
état SAT avec provenance
complétions
split sur variable
vérification terminale
premiers transports structurels
```

Gate : aucune requête SAT intermédiaire.

### Phase 9 - enrichissement relationnel SAT

Statut : futur.

Livrables :

```text
affaiblissement
renommage
symétrie
substitution
propagation
composition
```

Gate : chaque transformation est accompagnée d'une action constructive sur les complétions.

### Phase 10 - étude de largeur

Statut : futur.

Livrables :

```text
familles positives
familles séparatrices
mesure de largeur
mesure de taille de contexte
mesure de coût des recherches de transport
```

Gate : distinguer les résultats vérifiés en Lean des observations expérimentales.

### Phase 11 - audit P/NP

Cette phase ne peut commencer que si les phases précédentes donnent une instance SAT générale avec bornes prouvées.

Elle doit rechercher activement les endroits où une hypothèse contient déjà la difficulté NP.

La charge de preuve est entièrement du côté de la construction.

---

## 24. Stratégie d'expérimentation

Les expériences servent à chercher des séparateurs et des conjectures, pas à établir des théorèmes.

Pour une famille SAT donnée, enregistrer :

```text
nombre de variables
nombre de clauses
nombre de branches avant réduction
nombre de branches après réduction
nombre de transports trouvés
profondeur
largeur maximale
longueur des certificats
coût de recherche des transports
```

Chaque protocole confirmatoire devra respecter les règles de reproductibilité du dépôt.

Les heuristiques peuvent être explorées, mais aucune conclusion formelle ne doit dépendre d'une heuristique non certifiée.

---

## 25. Critères de réussite intermédiaires

Le chantier produit déjà un résultat utile si l'on obtient l'une des situations suivantes :

### Résultat A

Une nouvelle théorie générique de réduction de recherche par transports directionnels, indépendante de P/NP.

### Résultat B

Une caractérisation structurelle de classes de SAT ou CSP tractables par largeur constitutive bornée.

### Résultat C

Des séparateurs montrant précisément pourquoi certaines interfaces locales ne peuvent pas contrôler la largeur globale.

### Résultat D

Une reconstruction dynamique d'ancres montrant comment le chemin crée les relations utilisées pour sa propre continuation.

### Résultat E

Une borne non triviale sur une famille SAT jusque-là mal décrite par les interfaces testées.

Le chantier n'a donc pas besoin d'aboutir à P = NP pour avoir un contenu scientifique réel.

---

## 26. Conditions minimales avant toute revendication forte

Aucune phrase du type :

```text
SAT est en P
P = NP
```

ne doit apparaître comme conclusion scientifique du projet tant que les conditions suivantes ne sont pas toutes fermées.

1. L'instance couvre SAT général tel qu'annoncé.
2. Le split conserve exactement les complétions.
3. Chaque réduction est justifiée par un transport constructif.
4. Les transports sont reconstruits par une procédure explicitement définie.
5. Cette procédure n'utilise aucune décision SAT cachée.
6. Sa complétude nécessaire est démontrée, pas supposée.
7. La profondeur est polynomialement bornée.
8. La largeur constitutive est polynomialement bornée.
9. La taille des états et contextes est polynomialement bornée.
10. La taille des témoins de transport est polynomialement bornée.
11. Le coût de recherche et de validation des transports est polynomialement borné.
12. La procédure complète est exécutable.
13. Les preuves Lean sont constructives et sans axiomes interdits.
14. Les séparateurs connus du chantier ne contredisent pas l'interface finale.
15. Un audit externe de la formalisation et du modèle de coût est effectué avant toute communication forte.

Si une seule de ces conditions manque, le statut doit rester conditionnel ou exploratoire.

---

## 27. Audit permanent de la direction de dépendance

À chaque nouvelle définition, poser les questions suivantes :

```text
Cette donnée est-elle réellement primitive ?
Peut-elle être reconstruite ?
Est-elle utilisée pour définir quelque chose dont elle dépend en réalité ?
Introduit-elle implicitement l'existence d'une solution ?
Introduit-elle implicitement une décision globale ?
Peut-on construire un séparateur où elle échoue mais où les couches précédentes restent valides ?
```

Ce questionnaire doit devenir un réflexe de développement.

---

## 28. Discipline de branche

La branche `research/constitutive-search` est une branche de recherche.

Pendant le chantier :

```text
commits petits et auditables
aucun merge vers main sans demande explicite
régressions ajoutées avec chaque nouvelle couche
un bloc AXIOM_AUDIT par fichier Lean
aucun noncomputable
aucun Classical
aucun sorry
```

Avant une éventuelle pull request :

```text
supprimer ce document de chantier ou le convertir en document scientifique canonique
mettre à jour les versions française et anglaise si une documentation canonique est ajoutée
mettre à jour le manifeste
vérifier lake build
vérifier AuditRegression
scanner noncomputable
vérifier les audits axiomatiques
nettoyer tout fichier temporaire
```

---

## 29. Prochaine séquence d'implémentation

Ordre recommandé immédiat :

```text
1. DynamicAnchors
2. FrontierHistory
3. séparateur distinction sans transport
4. séparateur transport existant mais non trouvé
5. composition de réductions avec provenance
6. StructuralProgress
7. ConstitutiveWidth
8. premier mini-système exécutable non SAT
9. SAT.State et SAT.Completion
10. SAT.BinarySplit
11. WeakeningTransport
12. RenamingTransport
13. premières expériences de largeur
```

Le premier objectif concret est de montrer sur un système fini simple que :

```text
une détermination produite à l'étape k
→ devient une ancre à l'étape k + 1
→ rend reconstructible un transport auparavant indisponible
→ réduit effectivement la frontière
```

Ce résultat démontrerait formellement le mécanisme central du programme :

> la trajectoire constituée modifie les relations disponibles et devient ainsi une partie effective du calcul qui produit sa propre continuation.

---

## 30. Résumé du programme

La chaîne scientifique visée est :

```text
états constitués
        ↓
espaces de complétions
        ↓
splits AND/OR exacts
        ↓
relations locales
        ↓
transports directionnels reconstructibles
        ↓
réduction sûre des alternatives
        ↓
frontière constitutive
        ↓
déterminations nouvelles
        ↓
ancres nouvelles
        ↓
relations nouvelles
        ↓
réductions nouvelles
        ↓
trajectoire comme calcul
        ↓
terminaison structurelle
        ↓
largeur dérivée
        ↓
coût dérivé
        ↓
instance SAT
```

Le problème central n'est pas de choisir directement la branche qui contient une solution.

Le problème central est de reconstruire suffisamment de transformations entre les futurs possibles pour que les alternatives puissent être absorbées sans connaissance préalable de leur positivité.

La question de complexité devient alors :

> la structure relationnelle ainsi constituée suffit-elle à maintenir, pour SAT général, une profondeur, une largeur, une représentation et un coût local tous polynomialement contrôlés ?

C'est cette question qui doit guider la branche, sans raccourci sémantique et sans introduire la réponse dans les hypothèses.
