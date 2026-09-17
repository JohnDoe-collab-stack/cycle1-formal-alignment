# Strategie auditee - NP AND/OR P et recherche constitutive par trajectoire

## Statut du document

Ce document est le plan scientifique de travail de la branche research/np-and-or-p.

Base scientifique auditee avant cette revision :

~~~text
44f1bfc1d134b7e40b7ec4cd91eaed15f2f521cc
~~~

Ce commit a passe les gates Linux et Windows du projet, y compris le build Lean, AuditRegression et les controles de manifeste.

Le document est un document de chantier. Il ne constitue aucune revendication sur P = NP. Sa fonction est de distinguer exactement :

~~~text
ce qui est formalise
ce qui est seulement suggere par les exemples
ce qui reste a construire
ce qui doit etre falsifie
ce qui doit etre compare a la litterature
~~~

La priorite de cette revision est de ne pas confondre architecture elegante et resultat de complexite.

---

## 1. Probleme scientifique exact

Le point de depart n'est pas une lecture ensembliste de l'expression NP AND/OR P.

La lecture operationnelle visee est :

~~~text
OR
= ouverture de plusieurs continuations possibles

AND
= accumulation de determinations et de contraintes constituees

P
= calcul structurel effectif capable de reconstruire des relations
  entre certaines continuations

NP
= espace de recherche dans lequel une continuation acceptee
  n'est pas connue a l'avance
~~~

L'hypothese directrice est que le calcul ne doit pas etre pense comme la visite d'un chemin deja donne.

Le chemin est constitue pendant le calcul.

Une determination nouvelle modifie l'etat, l'historique disponible, les relations reconstructibles et donc les reductions possibles aux etapes suivantes.

La chaine cible est :

~~~text
etat constitue
-> continuations structurelles
-> acceptation eventuelle
-> relations reconstructibles
-> transports entre continuations
-> preservation de l'acceptation
-> absorption certifiee
-> nouvelle frontiere
-> nouvelle determination
-> nouvel espace relationnel
-> nouvelle etape
~~~

Le probleme central est donc :

> construire suffisamment de transformations positives entre futurs possibles pour reduire les alternatives sans connaitre a l'avance quelle branche est acceptee.

---

## 2. Discipline methodologique

Le programme suit la discipline :

~~~text
affaiblir
-> separer
-> reconstruire
-> composer
-> falsifier
~~~

Une propriete forte ne doit jamais etre introduite uniquement parce qu'elle rend une preuve possible.

En particulier, une reduction de branche ne peut pas prendre comme primitive :

~~~text
cette branche est satisfiable
cette branche est insatisfiable
une solution existe ici
aucune solution n'existe ici
le bon choix est cette branche
~~~

Un none retourne par une recherche structurelle signifie seulement :

~~~text
cette procedure n'a pas trouve ce witness
~~~

Il ne signifie jamais :

~~~text
aucun witness de cette nature n'existe
~~~

sans theorem de completude explicite.

---

## 3. Etat reel du code

### 3.1 Noyau generique formalise

Les modules suivants sont integres au build :

~~~text
ConstitutiveSearch/ContinuationTransport.lean
ConstitutiveSearch/FrontierReduction.lean
ConstitutiveSearch/RelationalTransport.lean
ConstitutiveSearch/IrreducibleFrontier.lean
ConstitutiveSearch/ConstitutiveWidth.lean
ConstitutiveSearch/FiniteFrontierNormalization.lean
ConstitutiveSearch/FrontierPreservation.lean
~~~

Ils fournissent actuellement :

~~~text
transport directionnel de Completion
composition de transports
split binaire exact
frontiere proof-relevant
absorption gauche et droite
recherche executable de relations
classification directionnelle
irreductibilite relative a une recherche
reduction certifiee de paire
largeur derivee
normalisation constructive d'une frontiere finie
preservation de frontiere dans les deux sens
equivalence constructive de Nonempty entre source et retenue
~~~

FrontierPreservation est maintenant formalise.

Le retour de la frontiere retenue vers la source n'est pas un inverse du transport d'absorption. Dans une absorption, il s'agit seulement de l'inclusion structurelle du survivant dans la frontiere d'origine.

### 3.2 Instance SAT formalisee

Les modules SAT suivants sont integres au build :

~~~text
ConstitutiveSearch/SAT/ConstraintTransport.lean
ConstitutiveSearch/SAT/BinaryBranch.lean
ConstitutiveSearch/SAT/RestrictionTransport.lean
ConstitutiveSearch/SAT/ResidualFlipTransport.lean
ConstitutiveSearch/SAT/ResidualTrajectory.lean
ConstitutiveSearch/SAT/BranchContext.lean
ConstitutiveSearch/SAT/BranchContextTransport.lean
ConstitutiveSearch/SAT/GeneratedContext.lean
ConstitutiveSearch/SAT/GlobalContextRelation.lean
~~~

Ils fournissent actuellement :

~~~text
syntaxe CNF minimale
satisfaction constructive
affaiblissement de CNF
split booleen exact
residuel faible de branche
reconstruction parent/residuel
flip de polarite
transport entre residuels
trajectoire residuelle lineaire
historique explicite de decisions
contexte de branche recursif
reconstruction positive des carriers
transport entre enfants avec preservation de provenance
etat uniforme GeneratedBranchContext
provenance inductive depuis la racine
reconstruction derivee de cette provenance
frontieres heterogenes de contextes generes
relation globale de flip entre contextes de parents differents
normalisation de frontiere heterogene par ce moteur de flip
~~~

La regression globale actuelle verifie notamment qu'un transport entre deux etats de profondeur deux provenant de parents immediats differents peut :

~~~text
modifier la decision x0
preserver la decision x1
reconstruire un vrai carrier cible
reduire la paire heterogene
preserver l'existence de completion dans les deux sens
~~~

Cette couche est formalisee et auditee sans axiome interdit.

---

## 4. Ce que les resultats actuels etablissent, et ce qu'ils n'etablissent pas

### 4.1 Ce qui est etabli

Le projet dispose maintenant d'une architecture constructive dans laquelle :

~~~text
des espaces proof-relevant sont indexes par des etats
des splits produisent plusieurs branches
des relations structurelles produisent des transports directionnels
des branches transportables peuvent etre absorbees
une normalisation finie construit une frontiere irreductible
la provenance des survivants permet un retour vers la frontiere source
des branches SAT recursives conservent leur historique
des relations peuvent comparer des branches de parents differents
~~~

### 4.2 Ce qui n'est pas etabli

Le projet ne montre pas actuellement :

~~~text
que SAT general a petite largeur
que la largeur actuelle est intrinsique
que la recherche de transports est polynomialement bornee
que les transports disponibles sont complets
que la composition de transports est exploree exhaustivement
que les etats ou certificats restent petits
que la profondeur globale est polynomialement bornee
que les exemples de flip generalisent a SAT arbitraire
~~~

Il ne faut donc tirer aucune conclusion sur P = NP.

---

## 5. Verrou semantique prioritaire P0 : separer continuation et acceptation

C'est maintenant le probleme scientifique le plus important du noyau actuel.

Dans ConstraintTransport.lean, la definition actuelle est :

~~~lean
abbrev Completion (formula : Cnf) : Type :=
  { assignment : Assignment // Satisfies assignment formula }
~~~

Le type Completion formula ne represente donc pas toutes les continuations structurellement possibles.

Il represente deja les affectations acceptees.

Les transports generiques actuels sont par consequent des transformations entre espaces de temoins acceptants.

Les transports concrets deja construits, comme le weakening ou le flip, restent des constructions legitimes. Le probleme est plus general : l'interface generique n'impose pas qu'un transport soit defini sur les continuations rejetees.

Cela empeche encore d'interpreter le noyau comme un modele complet de calcul de recherche.

### 5.1 Architecture cible

Introduire une separation explicite :

~~~lean
structure SearchSystem where
  State : Type
  Continuation : State -> Type
  Accept : (state : State) -> Continuation state -> Prop
~~~

Puis :

~~~lean
def Viable
    (system : SearchSystem)
    (state : system.State) : Prop :=
  Exists fun continuation =>
    system.Accept state continuation
~~~

Le transport semantiquement sur doit avoir la forme conceptuelle :

~~~lean
structure AcceptingContinuationTransport
    (system : SearchSystem)
    (source target : system.State) where
  map :
    system.Continuation source ->
    system.Continuation target
  preservesAccept :
    forall continuation,
      system.Accept source continuation ->
      system.Accept target (map continuation)
~~~

Le point essentiel est que map est total sur toutes les continuations structurelles, pas uniquement sur les temoins deja acceptes.

### 5.2 Specialisation SAT cible

Pour SAT, une cible naturelle est :

~~~text
Continuation formula = Assignment
Accept formula assignment = Satisfies assignment formula
~~~

Pour un contexte de branche, une version plus structurelle est possible :

~~~text
Continuation context
= affectation portant la preuve qu'elle respecte les decisions constituees

Accept context continuation
= cette affectation satisfait la formule residuelle
~~~

Ainsi :

~~~text
provenance structurelle
!=
acceptation SAT
~~~

La reconstruction d'un contexte genere devrait alors dependre de la provenance structurelle, et non d'une preuve de satisfaction necessaire pour fabriquer le carrier.

### 5.3 Separateur obligatoire

Construire un separateur minimal :

~~~text
Continuation source = Unit
Continuation target = Unit
Accept source _ = True
Accept target _ = False
~~~

Une fonction brute Unit -> Unit existe.

Mais aucun transport correct ne peut prouver preservesAccept.

Ce separateur doit montrer formellement pourquoi :

~~~text
fonction entre continuations
~~~

et :

~~~text
transport preservant l'acceptation
~~~

sont deux notions distinctes.

### 5.4 Gate P0

Aucune revendication forte sur la largeur, une procedure de decision ou la complexite ne doit utiliser l'ancien Completion comme s'il s'agissait deja d'un espace neutre de continuations.

La migration peut etre faite en parallele du noyau actuel afin de conserver les regressions comme oracle de comportement.

---

## 6. Preservation de frontiere : statut ferme dans l'ancien noyau

FrontierPreservation.lean fournit deja deux transports independants :

~~~text
source -> target
target -> source
~~~

sans loi d'inversion.

Il en derive :

~~~text
Nonempty source <-> Nonempty target
~~~

dans la semantique actuelle des Completion.

Apres la separation Continuation/Accept, la cible devra devenir :

~~~text
Viable source <-> Viable target
~~~

pour les frontieres.

Cette migration est prioritaire avant FrontierTrajectory, afin que la trajectoire soit construite directement sur la semantique correcte.

---

## 7. Etat SAT global et provenance : statut actuel

GeneratedContext.lean ferme le verrou d'homogeneisation des branches recursives.

Un GeneratedBranchContext rootFormula peut representer des etats provenant de parents differents tout en conservant une provenance inductive depuis la racine.

La reconstruction est derivee de cette provenance.

Elle n'est pas ajoutee comme hypothese arbitraire.

GlobalContextRelation.lean ferme ensuite le premier verrou relationnel global.

Le witness actuel GeneratedFlipAtRelation exige :

~~~text
formule cible
= flip de la formule source

historique cible
= flip de tout l'historique source
~~~

Il peut agir entre deux etats generes de la meme racine sans parent immediat commun.

Limite importante :

> il s'agit encore d'une famille precise de relations globales, le flip exact. Ce n'est pas encore un calcul general de dominance entre contextes.

---

## 8. Largeur : hierarchie a conserver

### 8.1 Largeur d'un certificat

Deja formalisee :

~~~text
nombre d'etats retenus par cette reduction precise
~~~

### 8.2 Largeur operationnelle

Deja calculable avec la normalisation actuelle.

Elle depend de :

~~~text
la recherche de relations
l'ordre de la frontiere
la strategie de normalisation
les generateurs disponibles
~~~

normalizedWidth ne doit pas etre appelee sans qualification "largeur du probleme".

### 8.3 Largeur fermee par composition

A construire.

Une frontiere irreductible sous recherche directe peut devenir reductible apres composition de transports.

### 8.4 Largeur minimale certifiable

A envisager seulement comme mesure mathematique secondaire.

Elle ne doit pas devenir une primitive algorithmique, car sa recherche peut elle-meme etre difficile.

---

## 9. Prochain grand objet P1 : trajectoire complete de frontieres

Une trajectoire doit faire du chemin un objet de calcul explicite.

Un pas cible doit contenir :

~~~text
frontiere source
choix structurel de l'expansion
split exact
frontiere developpee
reduction certifiee
frontiere retenue
preservation de viabilite
~~~

Conceptuellement :

~~~text
F_k
-> expansion
G_k
-> reduction
F_(k+1)
~~~

Une histoire de frontieres doit composer ces pas :

~~~text
F_0 -> F_1 -> ... -> F_n
~~~

### Theoremes prioritaires

Prouver constructivement :

~~~text
Viable F_0 <-> Viable F_n
~~~

dans le noyau semantiquement durci.

Deriver aussi la suite :

~~~text
width(F_0), width(F_1), ..., width(F_n)
~~~

puis la largeur maximale observee le long de cette trajectoire.

La largeur doit etre une propriete derivee du calcul effectivement construit.

Elle ne doit pas piloter retroactivement le calcul.

---

## 10. P2 : fermeture et composition des transports

Le noyau sait deja composer deux transports connus.

Il ne possede pas encore une syntaxe finie des transports admissibles ni une recherche explicite dans leur fermeture.

### 10.1 TransportCode

Introduire progressivement une syntaxe de codes :

~~~text
identity
weakening
flip
renaming
substitution
local rewrite
composition
~~~

avec :

~~~text
evalCode
soundCode
codeSize
~~~

L'objectif est d'eviter qu'une fonction Lean arbitraire soit traitee comme un certificat de cout constant.

### 10.2 Chemins de transports

Definir un objet proof-relevant :

~~~text
TransportPath A B
~~~

construit depuis les generateurs autorises.

Distinguer :

~~~text
existence mathematique d'un chemin
recherche executable d'un chemin
cout de cette recherche
~~~

### 10.3 Separateur direct/compose

Construire un exemple ou :

~~~text
A -> B
B -> C
~~~

sont reconstruits, alors que la recherche directe annoncee ne trouve pas A -> C.

Ce separateur doit empecher toute confusion entre irreductibilite directe et irreductibilite sous fermeture.

---

## 11. P3 : ancres dynamiques

C'est le test le plus direct de l'idee :

~~~text
le chemin est le calcul
~~~

Il faut construire un exemple ou :

~~~text
au niveau k
aucun transport n'est reconstruit entre deux branches

une determination nouvelle est constituee

cette determination ajoute une relation, une ancre ou une provenance utilisable

au niveau k+1
un transport devient reconstructible

ce transport reduit la frontiere
~~~

Une ancre dynamique n'a d'interet que si elle change effectivement la capacite de reconstruction.

Ajouter un label sans modifier les transformations disponibles ne suffit pas.

---

## 12. Semantique du residuel SAT actuel

branchResidual implemente actuellement un residuel faible.

Pour une valeur de branche, il :

~~~text
supprime une clause si elle contient le litteral rendu vrai
conserve les autres clauses
ne supprime pas encore le litteral rendu faux dans les clauses restantes
~~~

Ce n'est pas la restriction CNF standard completement simplifiee.

Cette distinction doit rester explicite.

### Extension future

Construire separement :

~~~text
residuel faible actuel
restriction CNF standard
transport ou equivalence entre leurs semantiques
~~~

Dans le noyau Continuation/Accept, cette comparaison devra etre exprimee au niveau des affectations et de la preservation d'acceptation.

---

## 13. P4 : progression structurelle et terminalite

La terminaison ne doit pas etre postulee par un compteur externe.

Pour SAT, la cible naturelle est :

~~~text
variables pertinentes de l'instance initiale
decisions sur variables fraiches
aucune repetition d'une variable le long d'une histoire legale
chaque etape non terminale ajoute une decision nouvelle
~~~

Il faut ensuite deriver une borne de profondeur depuis le nombre fini de variables pertinentes.

La fraicheur est un invariant de transition.

Elle ne doit pas etre justifiee retroactivement par la longueur de l'histoire.

---

## 14. Calcul des transports SAT

Chaque generateur doit fournir au minimum :

~~~text
witness structurel fini
action totale sur les continuations
preuve de preservation d'acceptation
procedure executable de recherche
preuve de correction positive
taille du witness
cout de verification
~~~

### Deja presents dans l'ancien noyau

~~~text
weakening
flip de polarite
lift du flip au contexte
flip global entre contextes generes
~~~

### Prochains generateurs a tester

~~~text
renommage fini de variables
restriction CNF standard
substitutions directionnelles
propagation certifiee
rewrites locaux
composition mediee
~~~

Aucun generateur ne doit etre ajoute seulement parce qu'il reduit la largeur sur un exemple.

Il doit posseder une justification structurelle autonome.

---

## 15. P5 : familles positives

Avant SAT general, il faut obtenir des theoremes parametriques.

### 15.1 Famille symetrique

Premiere cible :

~~~text
(x_i OR y_i)
AND
(NOT x_i OR y_i)
~~~

ou une variante exactement adaptee a la semantique formalisee.

Objectif :

> pour une famille de taille arbitraire, chaque split sur x_i produit des branches reliees par un transport explicite et la strategie choisie garde une largeur operationnelle controlee.

### 15.2 Famille exigeant composition

Construire ensuite une famille ou weakening ou flip seul ne suffit pas, mais ou une composition explicite controle la frontiere.

### 15.3 Classes connues

Seulement apres ces benchmarks :

~~~text
2-SAT
Horn-SAT
CSP de largeur bornee
CNF de treewidth ou pathwidth controlee
~~~

Le but n'est pas de redemontrer artificiellement leur tractabilite.

Le but est de determiner ce que mesure exactement la largeur constitutive.

---

## 16. P5 : separateurs et tentatives de falsification

Les separateurs sont obligatoires.

### 16.1 Separateur semantique

Fonction brute entre continuations mais absence de preservation d'acceptation.

### 16.2 Aucun transport trouve

Frontiere qui croit parce que le moteur relationnel annonce ne reconstruit aucune absorption.

### 16.3 Weakening insuffisant

Branches incomparables par weakening mais comparables par un autre generateur.

### 16.4 Flip insuffisant

Famille asymetrique ou le flip exact echoue.

### 16.5 Direct contre compose

Frontiere directement irreductible mais reductible par chemin de transports.

### 16.6 Sensibilite a l'ordre

Deux ordres de la meme frontiere produisent des representants differents, et si possible des largeurs operationnelles differentes.

Si la largeur ne peut pas differer sous les invariants du normaliseur, le prouver.

### 16.7 Provenance incompatible

Deux etats de meme lecture syntaxique apparente mais d'histoires incompatibles pour le calcul relationnel annonce.

### 16.8 Petite largeur, gros certificats

Exemple ou la frontiere reste petite mais la taille des witnesses explose.

### 16.9 Progression locale sans borne utile

Systeme abstrait avec etapes strictes mais profondeur globale non controlee.

### 16.10 Ancres inertes

Exemple ou l'historique grossit sans rendre aucun nouveau transport reconstructible.

Ce separateur est important pour eviter d'identifier automatiquement provenance et puissance algorithmique.

---

## 17. Hypothese de necessite : dans quel sens cette architecture pourrait-elle etre inevitable ?

L'intuition forte du programme est qu'une elimination correcte sans oracle negatif doit etre justifiee par une transformation positive des futurs.

Ce point n'est pas encore un theorem.

Il faut eviter un resultat circulaire qui definirait une elimination comme un transport puis conclurait qu'une elimination est un transport.

### 17.1 Theorem de necessite ambitieux

Chercher une specification externe d'une procedure d'elimination qui ne mentionne pas :

~~~text
transport
dominance
map de continuations
~~~

et qui impose seulement des proprietes operationnelles comme :

~~~text
constructivite
correction de l'elimination
possibilite de reconstruire un temoin cible depuis une execution source acceptee
composition des etapes
absence de decision generale de viabilite comme primitive
~~~

Puis montrer qu'une telle elimination induit une transformation totale sur les continuations avec preservation d'acceptation.

### 17.2 Alternatives a classifier

Une branche peut aussi etre supprimee par un certificat negatif explicite.

Le programme doit donc distinguer au minimum :

~~~text
elimination par transport positif
elimination par refutation locale certifiee
elimination par contradiction structurelle
~~~

La these "le transport est inevitable" ne peut etre defendue que relativement a une classe d'eliminations qui exclut ou reinterprete explicitement les certificats negatifs.

### 17.3 Necessite de provenance

Une cible plus concrete et probablement plus accessible consiste a construire deux etats ayant la meme lecture residuelle mais des historiques differents, puis a montrer que les transports admissibles different.

Un tel separateur montrerait :

~~~text
etat futur non determine par le residuel seul
=>
la provenance doit appartenir a l'etat operationnel
~~~

Cette cible testerait directement la proposition :

~~~text
le chemin est le calcul
~~~

sans supposer la conclusion.

---

## 18. Procedure de decision : correction avant complexite

Une procedure complete doit distinguer :

~~~text
preservation pendant le calcul
interpretation terminale
~~~

Apres le durcissement semantique, chaque etape devra conserver la viabilite de la frontiere.

A la fin, la decision terminale doit etre executable directement sur les continuations terminales.

Pour SAT :

~~~text
frontiere initiale
-> splits et reductions
-> frontiere terminale
-> affectations terminales
-> verification directe
~~~

La verification finale ne doit jamais guider retroactivement la construction des transports.

---

## 19. P6 : couche de complexite

La complexite ne commence qu'apres :

~~~text
separation Continuation/Accept
trajectoire correcte
fermeture de transports explicite
progression et terminalite
premieres familles positives et negatives
~~~

Les quantites a formaliser sont :

~~~text
taille d'entree
profondeur
largeur operationnelle maximale
taille d'etat
taille de provenance
taille des codes de transport
cout de recherche d'un transport
cout de recherche dans la fermeture
cout de normalisation
cout de verification terminale
~~~

Theorem conditionnel cible :

> si toutes ces quantites sont polynomialement bornees dans la taille de l'entree pour une procedure executable donnee, alors le cout total de cette procedure est polynomial.

Ce theorem ne fournit aucune des bornes.

Il ne fait qu'assembler des bornes deja prouvees.

---

## 20. Audit de litterature et de nouveaute

Le programme a plusieurs voisins conceptuels serieux.

### 20.1 P-selectivity et self-reducibility

Le resultat classique "P-selective + self-reducible implique P" est un garde-fou majeur.

Reference :

- H. Buhrman, E. van Helden, L. Torenvliet, P-Selective Self-Reducible Sets: A New Characterization of P, JCSS 53(2), 1996, DOI 10.1006/jcss.1996.0062.

Consequence methodologique :

> si notre mecanisme devient un selecteur polynomial uniforme sur une structure self-reducible, il faut verifier immediatement si le resultat est deja couvert par cette theorie.

### 20.2 Simulations, dominance et antichaines

Les reductions d'espaces d'etats par preordres de simulation et antichaines sont un voisin direct.

Reference de depart :

- M. De Wulf, L. Doyen, T. A. Henzinger, J.-F. Raskin, Antichains: A New Algorithm for Checking Universality of Finite Automata, CAV 2006, DOI 10.1007/11817963_5.

Questions a comparer :

~~~text
notre transport est-il une simulation standard dans certaines instances ?
la frontiere irreductible est-elle une antichain sous un preorder connu ?
la provenance dynamique change-t-elle le preorder lui-meme ?
~~~

Le dernier point est potentiellement distinctif et doit etre teste formellement.

### 20.3 CSP de largeur bornee

La litterature sur la coherence locale et la bounded width montre qu'une information locale suffisamment riche peut controler globalement certaines recherches.

Reference de depart :

- M. Kozik, Solving CSPs Using Weak Local Consistency, SIAM Journal on Computing, DOI 10.1137/18M117577X.

Il faut comparer :

~~~text
largeur constitutive
largeur de decomposition
coherence locale
polymorphismes
~~~

sans supposer qu'il s'agit de la meme notion.

### 20.4 Autres comparaisons obligatoires

~~~text
BDD et OBDD
branching programs
treewidth et pathwidth
subsumption
DPLL et CDCL
complexite des preuves
symmetry breaking SAT
memoisation et dynamic programming sur decompositions
~~~

Aucune revendication de nouveaute conceptuelle ne doit preceder cet audit.

---

## 21. Gates anti-triche

### Gate A - separation semantique

Les continuations structurelles et leur acceptation doivent etre des objets distincts avant toute analyse de complexite forte.

### Gate B - aucune decision SAT cachee

La reconstruction d'un transport ne peut pas appeler une decision generale de satisfaisabilite ou d'insatisfaisabilite.

### Gate C - totalite structurelle

Un transport annonce comme transformation de continuations doit etre defini sur toutes les continuations de son domaine structurel.

### Gate D - preservation d'acceptation

La correction semantique du transport doit etre un theorem explicite.

### Gate E - witness positif

Toute absorption positive doit etre accompagnee d'un witness structurel effectif.

### Gate F - none est relatif

Un echec de recherche n'est pas une inexistence mathematique.

### Gate G - provenance des survivants

Une continuation terminale doit rester interpretable dans la frontiere source.

### Gate H - pas de quotient gratuit

Deux etats de meme formule residuelle ne sont pas identifies sans theorem justifiant l'oubli de provenance.

### Gate I - fermeture annoncee

L'irreductibilite doit etre qualifiee relativement a la classe de transports effectivement exploree.

### Gate J - largeur qualifiee

Toujours preciser s'il s'agit de largeur :

~~~text
d'un certificat
operationnelle
fermee par composition
minimale abstraite
~~~

### Gate K - representation

Une petite largeur ne suffit pas si les etats, histoires ou codes de transport sont grands.

### Gate L - progression

Une transition stricte ne suffit pas sans borne globale de profondeur.

### Gate M - execution constructive

Aucun sorry, axiom, noncomputable ou Classical interdit dans les couches executables.

### Gate N - generalite

Une conclusion sur SAT general exige des theoremes couvrant toute la classe annoncee, pas seulement des familles symetriques.

### Gate O - terminalite independante

La verification terminale ne peut pas etre utilisee pour construire retroactivement le chemin.

---

## 22. Architecture Lean revisee

### 22.1 Existant et valide

~~~text
ConstitutiveSearch/
  ContinuationTransport.lean
  FrontierReduction.lean
  RelationalTransport.lean
  IrreducibleFrontier.lean
  ConstitutiveWidth.lean
  FiniteFrontierNormalization.lean
  FrontierPreservation.lean

ConstitutiveSearch/SAT/
  ConstraintTransport.lean
  BinaryBranch.lean
  RestrictionTransport.lean
  ResidualFlipTransport.lean
  ResidualTrajectory.lean
  BranchContext.lean
  BranchContextTransport.lean
  GeneratedContext.lean
  GlobalContextRelation.lean
~~~

### 22.2 Prochains modules prioritaires

Les noms sont provisoires.

~~~text
ConstitutiveSearch/
  SearchSystem.lean
  AcceptingTransport.lean
  AcceptedFrontier.lean
  AcceptedFrontierPreservation.lean
  FrontierTrajectory.lean
  TransportCode.lean
  TransportClosure.lean
  DynamicAnchors.lean
  StructuralProgress.lean
  ComplexityInterface.lean

ConstitutiveSearch/SAT/
  AcceptedSAT.lean
  AcceptedGeneratedContext.lean
  AcceptedGlobalContextRelation.lean
  ContextTrajectory.lean
  SimplifiedRestriction.lean
  RenamingTransport.lean
  SubstitutionTransport.lean
  PropagationTransport.lean
  ParametricSymmetricFamily.lean
  WidthSeparators.lean
~~~

Il est preferable d'introduire d'abord la semantique sure en parallele de l'ancien noyau, puis de migrer les regressions une par une.

---

## 23. Statut des phases

~~~text
[FAIT] noyau directionnel sur espaces de Completion actuels
[FAIT] frontieres proof-relevant
[FAIT] recherche relationnelle directe
[FAIT] normalisation finie
[FAIT] preservation de frontiere dans les deux sens
[FAIT] SAT minimal
[FAIT] provenance recursive SAT
[FAIT] GeneratedBranchContext
[FAIT] relation globale de flip entre parents differents

[P0] separation Continuation / Accept
[P0] migration de la preservation vers Viable
[P0] separateur fonction brute vs preservation d'acceptation

[P1] FrontierTrajectory
[P1] trajectoire SAT multi-niveaux

[P2] TransportCode
[P2] fermeture de transports
[P2] separateur direct vs compose

[P3] ancres dynamiques

[P4] progression structurelle et terminalite

[P5] familles parametriques positives
[P5] familles separatrices

[P6] tailles et couts
[P6] theorem conditionnel de complexite

[P7] audit de nouveaute approfondi
[P7] comparaison formelle avec notions voisines

[FERME] toute revendication P/NP avant fermeture de P0-P7
~~~

---

## 24. Sequence d'implementation immediate

Ordre recommande a partir du head actuel :

~~~text
1. creer le noyau SearchSystem avec Continuation et Accept
2. definir Viable
3. definir le transport total preservant Accept
4. construire le separateur Unit / True -> Unit / False
5. reconstruire le split exact au niveau des continuations
6. reconstruire la frontiere et sa viabilite
7. migrer FrontierPreservation vers Viable
8. instancier SAT avec Assignment comme continuation brute
9. reconstruire les contextes generes sans cacher satisfaction dans le carrier
10. migrer le flip global vers cette semantique
11. reproduire la regression heterogene actuelle dans le nouveau noyau
12. construire FrontierTrajectory
13. construire une trajectoire SAT a plusieurs niveaux avec reduction a chaque niveau
14. introduire TransportCode
15. introduire TransportClosure
16. construire le separateur direct vs compose
17. tester la sensibilite a l'ordre du normaliseur
18. construire le premier exemple d'ancre dynamique effective
19. prouver une famille SAT symetrique parametrique
20. construire les separateurs de largeur
21. prouver progression et borne de profondeur
22. seulement ensuite introduire tailles et couts
~~~

Le point 1 remplace maintenant FrontierTrajectory comme prochain verrou.

La raison est semantique : une trajectoire globale construite sur des carriers contenant deja l'acceptation serait formellement correcte dans l'ancien modele, mais scientifiquement trop faible pour porter ensuite une interpretation de complexite.

---

## 25. Premier theorem global vise apres P0

Forme cible :

> Pour toute trajectoire finie construite par splits structurels exacts et absorptions certifiees par des transports preservant l'acceptation, la viabilite de la frontiere initiale est equivalente a la viabilite de la frontiere finale.

Forme conceptuelle :

~~~text
ViableFrontier F0 <-> ViableFrontier Fn
~~~

sans exiger que les transports d'absorption soient inversibles.

---

## 26. Premier theorem SAT parametrique vise

Apres le theorem de trajectoire :

> Une famille parametrique de CNF a symetries locales explicites admet une trajectoire de contextes dans laquelle chaque split sur une variable fraiche est suivi d'une absorption certifiee, et la largeur operationnelle reste bornee par une constante explicite sous la strategie annoncee.

Le theorem doit porter sur une famille de taille arbitraire.

Une regression fermee ne suffit pas.

---

## 27. Premiers theoremes separateurs vises

Deux separateurs sont prioritaires.

Premier separateur :

> une fonction totale entre continuations peut exister sans transport preservant l'acceptation.

Deuxieme separateur :

> sous un moteur relationnel R annonce, une frontiere peut etre directement irreductible alors qu'un chemin de transports elementaires permet une reduction apres fermeture.

Ces deux resultats testent respectivement :

~~~text
la semantique du transport
la semantique de l'irreductibilite
~~~

---

## 28. Criteres de valeur scientifique independants de P/NP

Le chantier a un interet propre si l'un ou plusieurs des resultats suivants sont obtenus :

~~~text
A. theorie constructive de reduction par transports preservant l'acceptation
B. provenance de frontiere composee de bout en bout
C. hierarchie propre de notions de largeur
D. theoremes parametriques sur des familles de contraintes
E. separateurs d'interfaces relationnelles
F. ancres dynamiques changeant reellement les transports disponibles
G. theorem de necessite ou separateur de necessite de provenance
H. correspondance ou separation avec simulations, antichaines, CSP ou branching programs
~~~

Ces resultats seraient scientifiquement interpretables meme si aucune consequence sur P et NP n'etait obtenue.

---

## 29. Conditions avant toute revendication de complexite forte

Toutes les conditions suivantes doivent etre fermees.

1. Continuation et acceptation sont separees.
2. Les transports sont totaux sur les continuations structurelles.
3. La preservation d'acceptation est prouvee.
4. Les splits sont exacts structurellement.
5. Les reductions preservent la viabilite dans les deux sens.
6. La trajectoire globale est composee constructivement.
7. Les transports proviennent de witnesses ou codes finis explicites.
8. Les recherches n'utilisent aucune decision SAT cachee.
9. La fermeture effectivement utilisee est explicite.
10. La profondeur globale est bornee.
11. La largeur operationnelle globale est bornee.
12. La taille des etats est bornee.
13. La taille des historiques et ancres est bornee.
14. La taille des codes et witnesses est bornee.
15. Le cout de recherche relationnelle est borne.
16. Le cout de fermeture est borne.
17. Le cout de normalisation est borne.
18. La procedure terminale est executable et correcte.
19. Les preuves Lean respectent les contraintes constructives du depot.
20. Les familles separatrices pertinentes ont ete testees.
21. Le positionnement par rapport aux resultats connus a ete audite.
22. Toute revendication forte a ete relue independamment.

Si une seule condition manque, le statut reste conditionnel ou exploratoire.

---

## 30. Discipline de branche

Sur research/np-and-or-p :

~~~text
commits petits et auditables
regression avec chaque nouvelle couche
AXIOM_AUDIT dans chaque fichier Lean scientifique
aucun sorry
aucun noncomputable
aucun Classical interdit
aucun merge vers main sans demande explicite
~~~

Pour un changement structurel important :

~~~text
utiliser une branche de validation si necessaire
laisser Linux et Windows passer
fast-forward seulement apres validation
~~~

Avant toute pull request vers main :

~~~text
convertir ou supprimer ce document de chantier
mettre a jour la documentation canonique
verifier le manifeste
verifier lake build
verifier AuditRegression
verifier les audits axiomatiques
scanner sorry, axiom, noncomputable et Classical
nettoyer les branches ou fichiers temporaires
~~~

---

## 31. Resume du programme audite

Etat actuel :

~~~text
transport de witnesses acceptants
-> frontieres
-> absorption
-> normalisation
-> preservation bidirectionnelle de Nonempty
-> provenance SAT recursive
-> etat SAT global heterogene
-> relation globale entre parents differents
~~~

Correction scientifique prioritaire :

~~~text
separer continuations structurelles et acceptation
~~~

Puis :

~~~text
transport total preservant Accept
-> preservation de Viable
-> trajectoire de frontieres
-> codes et fermeture des transports
-> ancres dynamiques
-> progression
-> largeur le long de la trajectoire
-> familles positives et separatrices
-> tailles et couts
-> audit de necessite et de nouveaute
-> seulement ensuite audit de complexite forte
~~~

Le point central reste intact :

> le chemin n'est pas seulement la trace d'un calcul. Les determinations constituees pendant ce chemin peuvent changer les relations disponibles et donc changer le calcul lui-meme.

Le prochain travail ne consiste donc pas a ajouter encore un exemple de reduction locale.

Il consiste a durcir la semantique du noyau pour que cette idee puisse etre testee sans que l'acceptation soit deja enfouie dans le type des continuations.
