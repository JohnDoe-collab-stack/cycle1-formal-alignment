# Alignement constitutif des systèmes transformers

[English](../en/constitutive_transformer_alignment.md) | **Français**

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[méthode](methode_roles_constitutifs_relationnels.md) ·
[Cycle 1 — alignement relatif](alignement_relatif.md) ·
[Cycle 2 — alignement réflexif](alignement_reflexif.md)

## 1. Thèse

Une architecture transformer ne devient pas persistante, cohérente à long
terme ou fiable en ajoutant simplement davantage de contexte, une mémoire
externe ou un classificateur de sorties. Ces dispositifs opèrent sur des objets
qu'ils supposent déjà individués. Or le problème premier est de déterminer ce
qui fait qu'une occurrence demeure la même occurrence à travers sa formation,
sa transformation, sa compression, sa récupération et son emploi ultérieur.

L'hypothèse architecturale développée ici est la suivante :

> **Un système transformer doit constituer ses objets par les relations qui
> déterminent leur identité, puis démontrer la conservation de cette
> constitution à travers ses réalisations. La mémoire persistante, le
> raisonnement à horizon long et la prévention des hallucinations deviennent
> alors trois conséquences d'une même exigence de fidélité structurelle.**

Cette proposition transpose la méthode des rôles constitutifs relationnels.
Elle ne réduit pas ces rôles à des étiquettes ajoutées aux représentations d'un
modèle. Une étiquette décrit un objet tenu pour donné ; une relation
constitutive participe à la détermination de l'objet lui-même. Si cette relation
est supprimée ou altérée, ce n'est pas seulement une propriété de l'objet qui
change : le système ne dispose plus du même objet au sens pertinent pour son
histoire.

## 2. Point de départ formel

Le dépôt établit déjà une chaîne structurelle complète sur une première
instance :

```text
présentation
  → construction dépendamment typée
  → occurrences individuées dans une histoire
  → rôles et accords exacts
  → réalisation fidèle
  → régime opérationnel et norme autonome
  → adéquation exacte
  → continuation minimale fidèlement réalisable
  → sortie localisée du régime et de la norme
```

Le Cycle 2 transporte l'habitabilité des familles de témoins vers une couche de
représentation et démontre simultanément :

```text
représentation exacte de statuts déterminés
  + statut diagonal non représentable
  → absence de clôture réflexive globale
```

L'application aux transformers ne consiste donc pas à importer les noms de ces
structures dans une architecture existante. Elle consiste à construire une
seconde instance de la méthode, dont le carrier, les occurrences, les rôles,
les accords et les réalisations appartiennent réellement au domaine des
systèmes transformers.

## 3. L'objet fondamental n'est ni le token ni le vecteur

Un token isolé est une valeur de vocabulaire. Un vecteur d'activation est un
élément d'un espace numérique. Aucun des deux ne détermine à lui seul
l'occurrence dont le système doit conserver l'identité.

La même chaîne de caractères peut apparaître plusieurs fois avec des origines,
des dépendances et des fonctions différentes. Inversement, une même occurrence
peut être reformulée, distribuée entre plusieurs vecteurs ou réalisée dans des
supports différents sans cesser d'être la même occurrence structurelle.

Le carrier pertinent doit donc être une histoire de transformations typées :

```lean
State   : Type
Step    : State → State → Type
History : State → State → Type
```

Une occurrence n'est pas une valeur extraite après coup de cette histoire. Elle
est indexée par l'histoire qui l'a formée :

```lean
Occurrence : {a b : State} → History a b → Type
```

Cette dépendance conserve au minimum :

- l'étape de formation de l'occurrence ;
- son état source et son état cible ;
- sa position structurelle dans la trajectoire ;
- les occurrences dont sa formation dépend ;
- les obligations auxquelles elle participe ;
- les transformations par lesquelles elle a été réalisée.

Deux occurrences textuellement identiques restent alors distinctes lorsque
leurs formations diffèrent. Deux réalisations matériellement différentes
peuvent au contraire correspondre exactement à la même exigence constitutive
si un accord et un transport fidèles sont fournis.

## 4. Rôles constitutifs et accords

Un rôle n'est pas une classe comme `fact`, `memory`, `premise` ou `error`. Il
exprime une exigence relationnelle dont dépend la participation d'une occurrence
à la construction considérée.

Dans une trajectoire transformer, les rôles peuvent notamment déterminer :

- quelle transformation a formé l'occurrence ;
- de quelles occurrences antérieures elle dépend constitutivement ;
- quelle différence elle introduit dans l'état courant ;
- quelle provenance elle continue ou transforme ;
- quelle obligation elle ouvre, conserve ou satisfait ;
- à quelle composition elle participe effectivement ;
- quelles occurrences doivent la précéder ou lui être immédiatement adjacentes.

Cette liste n'est pas un schéma d'annotation. Chaque rôle retenu doit être
accompagné d'un type d'accord établissant qu'une occurrence donnée le réalise
effectivement. Le modèle du Cycle 1 est :

```lean
RequirementOccurrenceAgreement
  (history : History)
  (requirement : Requirement)
  (occurrence : Occurrence history) : Type
```

L'accord doit exposer les données qui rendent la correspondance exacte : états
source et cible, formation, dépendances, compatibilités, provenance ou autre
structure propre au domaine. L'identité ne provient donc jamais de la seule
déclaration que l'occurrence porte le bon rôle.

## 5. Réalisation exacte sans exhaustivité forcée

Pour une famille de rôles exigés par une construction, une réalisation exacte
doit fournir :

```lean
realize           : Role → Occurrence history
realize_injective : Injective realize
agreement         : ∀ role, Agreement role (realize role)
```

La couverture va des rôles exigés vers leurs occurrences. Elle ne dit pas que
toute occurrence produite par le transformer doit déjà recevoir l'un de ces
rôles. Cette asymétrie est essentielle : la construction peut continuer et
former de nouvelles occurrences sans que l'exactitude locale antérieure soit
effacée.

L'injectivité interdit que deux exigences constitutivement distinctes soient
réalisées par une seule occurrence sous prétexte qu'elles possèdent une
représentation voisine. L'accord interdit le défaut inverse : deux occurrences
distinctes ne deviennent pas fidèles du seul fait qu'elles sont séparées dans
la mémoire.

## 6. Le transformer comme réalisation

Le transformer n'est pas la source de la constitution. Il est une réalisation
possible d'une histoire déjà spécifiée au niveau structurel.

Il faut par conséquent distinguer trois trajectoires :

```text
histoire constitutive
  = formation des occurrences et de leurs dépendances

histoire d'exécution
  = transformations concrètes réalisées par l'architecture

trace de tokens
  = entrées et sorties discrètes d'une exécution particulière
```

Elles ne sont pas identifiées terme à terme. Une occurrence constitutive peut
être réalisée par plusieurs tokens et plusieurs états internes ; une même étape
de génération peut contribuer à plusieurs relations sans constituer à elle
seule une occurrence complète. La réalisation doit donc associer une occurrence
à un témoin d'exécution structuré, et non coller son nom sur un token ou un
vecteur.

Une réalisation concrète peut employer des tokens, des activations, des états
d'attention, un cache, une mémoire persistante ou plusieurs supports. Sa
fidélité ne dépend pas du support choisi, mais des applications et des lois qui
relient les occurrences libres aux occurrences concrètes :

```lean
forward  : FreeOccurrence history → ConcreteOccurrence realization
backward : ConcreteOccurrence realization → FreeOccurrence history

backward (forward occurrence) = occurrence
forward (backward concrete)   = concrete
```

Lorsque l'implémentation contient davantage de phénomènes concrets que ceux que
la spécification doit suivre, ces lois peuvent être restreintes à la fibre des
occurrences constitutivement pertinentes. Ce qui ne peut pas être remplacé est
la preuve que les occurrences suivies, leurs accords et leurs relations
nécessaires survivent au transport.

Une similarité vectorielle, une reconstruction linguistique plausible ou une
égalité de sortie terminale ne constitue pas cette preuve. Deux exécutions
peuvent aboutir à la même réponse tout en ayant perdu une dépendance, interverti
deux occurrences ou substitué une provenance à une autre.

La mémoire, le contexte et les activations sont ainsi des supports de
réalisation. Ils ne deviennent porteurs de continuité qu'à travers les lois qui
les relient à l'histoire constitutive.

## 7. Quatre couches irréductibles

Pour une histoire `H` et une continuation candidate `x`, l'architecture doit
maintenir quatre familles distinctes :

```text
C(H, x)   construction interne de x
F_A(H, x) réalisation fidèle de x dans l'implémentation A
R(H, x)   admission de x par le régime opérationnel
S(H, x)   satisfaction par x d'une norme autonome
```

Le générateur transformer produit des témoins de construction. Une réalisation
concrète fournit des témoins de fidélité. Le régime décide quelles
continuations sont admises dans une trajectoire donnée. La norme énonce
indépendamment ce que cette trajectoire doit satisfaire.

L'alignement relatif n'est ni un score, ni une préférence, ni une concordance
entre deux sorties. Il est constitué par les transformations de témoins :

```text
R(H, x) → S(H, x)    soundness
S(H, x) → R(H, x)    complétude relative
```

Les deux familles portent sur le même candidat finement individué. Définir la
norme à partir de la décision du régime rendrait l'adéquation tautologique et
supprimerait précisément le contrôle recherché.

## 8. Une origine structurelle commune des trois problèmes

### 8.1 Mémoire persistante

La mémoire persistante est la conservation d'occurrences constituées à travers
une succession de transformations. Elle n'est pas la simple disponibilité
ultérieure d'un texte ou d'un contenu similaire.

Une mémoire est fidèle lorsqu'elle permet de récupérer l'occurrence avec les
relations qui déterminent son identité dans l'histoire : formation, provenance,
dépendances et statut relativement aux obligations concernées. Une
reformulation ou une compression est admissible si elle réalise un transport
exact de cette structure. Sans ce transport, le système peut restituer une
information ressemblante tout en ayant perdu l'objet auquel le raisonnement
ultérieur devait se rapporter.

### 8.2 Raisonnement à horizon long

Un raisonnement long est une composition d'occurrences et d'obligations, pas
une grande quantité de texte intermédiaire. Sa continuité dépend de la
conservation de ce qui rend chaque étape participante à la trajectoire : ses
prémisses effectives, les transformations autorisées, les résultats acquis et
les obligations encore ouvertes.

L'horizon pertinent est donc structurel plutôt que métrique. Un raisonnement
peut être long en nombre de tokens tout en étant structurellement rompu très
tôt ; il peut être fortement comprimé tout en restant intact si les relations
constitutives nécessaires sont préservées.

### 8.3 Hallucination

Dans ce cadre, l'hallucination n'est pas primitivement un type de phrase ni un
label attribué à une sortie. Le phénomène pertinent apparaît lorsqu'une
continuation demeure constructible et concrètement réalisable alors que
l'accord requis par la norme autonome n'est plus disponible ou est
constructivement réfuté.

Le système ne doit pas supprimer cette continuation de l'espace de
construction : cela masquerait le phénomène. Il doit conserver sur le même
candidat :

```text
témoin de construction
+ témoin de réalisation fidèle
+ structure antérieure encore préservée
+ preuve de la première obligation rompue
```

L'hallucination devient ainsi un cas possible de sortie structurelle localisée.
La définition exacte dépend de la norme du domaine ; elle ne se confond ni avec
la seule inadmission opérationnelle, ni avec toute continuation hors régime.

## 9. Le diagnostic par sortie constitutive

Une architecture capable de continuer doit pouvoir représenter positivement ce
qui subsiste lorsqu'une frontière est franchie. Le schéma générique est :

```lean
structure RegimeExit (Faithful Regime : Carrier → Type) where
  candidate    : Carrier
  faithful     : Faithful candidate
  inadmissible : Regime candidate → False
```

Pour le domaine transformer, ce diagnostic doit être enrichi par la
continuation de l'histoire et, lorsque la norme le permet, par une réfutation
normative directe. L'objectif est d'obtenir un premier candidat tel que :

```text
il est formé par le système ;
il est strictement postérieur à une trajectoire admise ;
les occurrences antérieures restent exactement réalisées ;
la nouvelle occurrence reste concrètement réalisable ;
une obligation constitutive précise cesse d'être satisfaite ;
le régime et la norme rejettent cette continuation pour des raisons explicites.
```

Ce témoin constituerait l'analogue transformer de
`oneStepAfterPerimeter`. Il fournirait un diagnostic local sans nier que le
système a effectivement produit une continuation.

## 10. Une architecture dynamique et non close

Le Cycle 2 interdit de conclure de la représentation exacte de certains statuts
à la représentabilité interne de tous les statuts possibles. Pour un évaluateur

```lean
eval : Code → Code → Prop
```

le statut

```lean
diagonalStatus eval code := ¬ eval code code
```

n'est représenté exactement par aucune ligne de cet évaluateur. Cette
non-clôture ne détruit pas l'exactitude des statuts particuliers déjà
représentés.

Transposée architecturalement, cette conclusion écarte le projet d'un
transformer qui contiendrait une représentation totale et finale de la validité
de toutes ses propres constructions. Le système doit être dynamique, relatif
à des normes et des régimes déterminés, et capable de continuer en produisant
des sorties explicites lorsque ses frontières internes sont atteintes.

La réflexivité utile n'est donc pas une auto-certification globale. Elle est la
représentation exacte de statuts déterminés, accompagnée d'une architecture qui
reconnaît constitutivement sa non-clôture.

## 11. Programme formel

La seconde instance doit être développée dans l'ordre suivant.

### 11.1 Présentation transformer

Définir les états et les règles de formation sans inscrire dans ces règles le
régime ou la norme qui seront étudiés ensuite.

### 11.2 Occurrences dépendantes

Construire un type d'occurrences indexé par les histoires, capable de distinguer
les répétitions textuelles et de conserver leur formation.

### 11.3 Rôles et accords constitutifs

Définir un noyau minimal de rôles relationnels, puis tester sur des carriers
affaiblis quelles relations sont primitives et lesquelles sont reconstructibles.

### 11.4 Réalisation abstraite et concrète

Établir d'abord une interface indépendante de l'architecture numérique, puis
montrer comment une exécution transformer réalise exactement les occurrences
et leurs accords.

### 11.5 Composition des transports

Prouver que les transports successifs utilisés par l'attention, la compression,
la récupération et la réinjection conservent la fidélité. La composition doit
conserver les témoins, pas seulement une mesure terminale.

### 11.6 Régime, norme et adéquation

Définir les deux familles indépendamment et établir les applications de
soundness et de complétude sur un domaine déterminé.

### 11.7 Sortie minimale

Construire une continuation minimale qui préserve les témoins positifs tout en
localisant exactement la première rupture constitutive.

### 11.8 Couche réflexive

Transporter l'habitabilité des statuts adéquats vers une représentation interne
et intégrer la non-clôture diagonale sans l'assimiler à la sortie
opérationnelle.

## 12. Critère d'une première implémentation

Une première implémentation n'a pas pour fonction de découvrir empiriquement le
cadre. Elle doit réaliser une interface déjà définie et rendre auditables ses
obligations.

Elle est suffisante si elle permet :

1. de former une histoire de transformations ;
2. d'individuer chaque occurrence par sa formation ;
3. d'associer les rôles par des accords vérifiables plutôt que par des labels ;
4. de transporter les occurrences à travers au moins une réduction de
   représentation ;
5. de reconstruire les relations constitutives après ce transport ;
6. de distinguer construction, fidélité, régime et norme ;
7. de produire un candidat de sortie conservant ses témoins positifs ;
8. de localiser la première obligation rompue.

Le cas initial doit posséder une norme décidée avec suffisamment de précision
pour que les transformations de témoins soient constructibles. L'extension à
des normes ouvertes vient après cette instance exacte, et non à sa place.

## 13. Contribution visée

La contribution n'est pas une nouvelle variante de mémoire, de récupération ou
de vérification ajoutée à un modèle. Elle est une architecture de constitution
et de conservation dans laquelle :

- les objets sont individués par leur formation et leurs relations ;
- les représentations sont des réalisations soumises à des lois de fidélité ;
- la persistance signifie conservation de l'identité constitutive ;
- le raisonnement signifie composition conservée d'occurrences et
  d'obligations ;
- la rupture normative est localisée sans effacement de la construction ;
- l'exactitude locale demeure compatible avec la non-clôture réflexive globale.

Le résultat attendu est un système qui ne prétend pas rendre impossible toute
continuation hors norme. Il rend structurellement explicite ce qui est formé,
ce qui est conservé, ce qui est admis, ce qui satisfait la norme et le point
exact où ces dimensions cessent de coïncider.

## 14. Statut du document

Le dépôt actuel vérifie en Lean le noyau structurel, l'instance circulaire de
l'alignement relatif et le résultat de non-clôture réflexive. Le présent texte
détermine la transposition architecturale de ce cadre aux systèmes
transformers. Les déclarations propres à cette seconde instance devront être
ajoutées comme nouveaux objets Lean avant d'être présentées comme théorèmes sur
les transformers.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d'OpenAI, sous direction humaine et au cours
> d'interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
