# Strategie auditee - NP AND/OR P et recherche constitutive par trajectoire

## Statut du document

Ce document est le plan scientifique de travail de la branche research/np-and-or-p.

Base scientifique auditee actuelle avant cette mise a jour documentaire :

~~~text
23ca5f946d832a2878e234b81e7ece30d5e39975
~~~

P1, P2, P3 et la couche P4 de codes compositionnels sont compilees et axiom-free sur Linux. Le CI final de la presente mise a jour documentaire doit confirmer de nouveau l'ensemble sur Linux et Windows.

La consolidation GitHub est terminee : le chantier NP AND/OR P n'a plus qu'une branche canonique, research/np-and-or-p.

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

Les couches suivantes sont maintenant integrees au build :

~~~text
ConstitutiveSearch/ContinuationTransport.lean
ConstitutiveSearch/SearchSystem.lean
ConstitutiveSearch/AcceptingTransport.lean
ConstitutiveSearch/AcceptedSplit.lean
ConstitutiveSearch/AcceptedFrontier.lean
ConstitutiveSearch/AcceptedFrontierPreservation.lean

ConstitutiveSearch/FrontierReduction.lean
ConstitutiveSearch/RelationalTransport.lean
ConstitutiveSearch/IrreducibleFrontier.lean
ConstitutiveSearch/ConstitutiveWidth.lean
ConstitutiveSearch/FiniteFrontierNormalization.lean
ConstitutiveSearch/FrontierPreservation.lean
~~~

Le projet possede maintenant deux niveaux clairement distingues :

~~~text
ancien noyau
= reduction et normalisation sur espaces de Completion

noyau durci
= Continuation structurelle + Accept + Viable
  + transports totaux preservant Accept
  + splits exacts preservant Accept
  + frontieres et preservation de Viable
~~~

Le noyau durci etablit notamment :

~~~text
SearchSystem.State
SearchSystem.Continuation
SearchSystem.Accept
SearchSystem.Viable
AcceptedContinuation derive
AcceptingContinuationTransport total
preservesAccept separe de map
composition constructive
AcceptingExactBinarySplit
FrontierContinuation
FrontierAccept
FrontierViable
AcceptedFrontierPreservation
Viable source <-> Viable target
~~~

Le separateur anti-triche existe en regression : une fonction brute entre continuations peut exister sans fournir de transport preservant l'acceptation. Le fait de savoir transporter uniquement des temoins deja acceptes ne suffit pas non plus a reconstruire un transport structurel total.

### 3.2 Instance SAT durcie

Les modules SAT suivants sont maintenant integres au build :

~~~text
ConstitutiveSearch/SAT/ConstraintTransport.lean
ConstitutiveSearch/SAT/AcceptedSAT.lean
ConstitutiveSearch/SAT/AcceptedBinaryBranch.lean
ConstitutiveSearch/SAT/StructuralBranchContext.lean
ConstitutiveSearch/SAT/GeneratedStructuralContext.lean

ConstitutiveSearch/SAT/BinaryBranch.lean
ConstitutiveSearch/SAT/RestrictionTransport.lean
ConstitutiveSearch/SAT/ResidualFlipTransport.lean
ConstitutiveSearch/SAT/ResidualTrajectory.lean
ConstitutiveSearch/SAT/BranchContext.lean
ConstitutiveSearch/SAT/BranchContextTransport.lean
ConstitutiveSearch/SAT/GeneratedContext.lean
ConstitutiveSearch/SAT/GlobalContextRelation.lean
~~~

Dans la semantique durcie :

~~~text
Continuation SAT = Assignment
Accept formula assignment = Satisfies assignment formula
~~~

Les affectations rejetees appartiennent donc bien a l'espace structurel. La satisfaction n'est plus enfouie dans le carrier.

Le split SAT durci est exact sur toutes les affectations. Les enfants ajoutent seulement la decision booleenne correspondante. La preservation de satisfaction est prouvee separement.

StructuralBranchContext contient :

~~~text
formule residuelle
+
historique de decisions constituees
~~~

StructuralBranchContinuation contient :

~~~text
affectation totale
+
preuve qu'elle realise l'historique
~~~

StructuralBranchAccept contient uniquement :

~~~text
satisfaction de la formule residuelle
~~~

GeneratedStructuralContext ajoute une provenance inductive depuis une formule racine, impose la fraicheur des variables de branchement et donne un type uniforme pour des contextes produits a des profondeurs et par des parents differents.

Le split genere structurel est compile, audite et teste sur Linux et Windows.

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

## 5. P0 ferme : continuation structurelle et acceptation sont separees

Le verrou semantique principal identifie dans la revision precedente est maintenant ferme dans le nouveau noyau.

La structure centrale est :

~~~lean
structure SearchSystem where
  State : Type
  Continuation : State -> Type
  Accept : (state : State) -> Continuation state -> Prop
~~~

La viabilite est derivee :

~~~lean
Viable state :=
  Exists fun continuation =>
    Accept state continuation
~~~

Le transport durci est total sur l'espace structurel :

~~~lean
structure AcceptingContinuationTransport ... where
  map : Continuation source -> Continuation target
  preservesAccept :
    forall continuation,
      Accept source continuation ->
      Accept target (map continuation)
~~~

Le point fondamental est maintenant impose par les types :

~~~text
map
!=
preuve qu'une continuation est acceptee

Continuation
!=
temoin deja accepte
~~~

### 5.1 SAT

L'instance SAT utilise :

~~~text
Continuation formula = Assignment
Accept formula assignment = Satisfies assignment formula
~~~

Les regressions contiennent explicitement des continuations rejetees. Elles montrent qu'elles restent des objets structurels valides sans devenir artificiellement des witnesses SAT.

### 5.2 Provenance

Dans StructuralBranchContext, la provenance n'est pas une preuve de satisfaction.

Elle specifie seulement les decisions que la continuation doit realiser.

Donc :

~~~text
provenance structurelle
!=
acceptation
~~~

Cette separation est maintenant realisee dans Lean, et non seulement posee comme objectif.

### 5.3 Separateurs deja formalises

Les regressions etablissent les distinctions suivantes :

~~~text
fonction brute
!=
transport preservant Accept

transport entre accepted witnesses
!=
transport total sur continuations structurelles

continuation structurelle
!=
continuation acceptee
~~~

Ces separateurs sont des garde-fous permanents pour la suite.

## 6. Preservation de frontiere : ancien noyau et noyau durci

L'ancien FrontierPreservation reste utile comme couche historique et comme oracle de comportement.

Le nouveau AcceptedFrontierPreservation porte la propriete pertinente dans la semantique separee :

~~~text
FrontierViable source <-> FrontierViable target
~~~

Il combine deux transports independants :

~~~text
source -> target
target -> source
~~~

sans exiger qu'ils soient inverses.

Les expansions par split exact et les absorptions par transport preservant Accept disposent maintenant d'une preservation constructive de viabilite.

Le prochain moteur automatique doit utiliser cette couche durcie plutot que reconstruire une trajectoire globale sur les anciens Completion.

## 7. Etat SAT global, provenance et constitution dynamique

Le projet dispose maintenant de deux generations de contexte SAT :

~~~text
GeneratedContext
= premiere couche globale proof-relevant sur l'ancien noyau

GeneratedStructuralContext
= couche globale durcie sur Continuation / Accept separes
~~~

GeneratedStructuralContext est maintenant la base semantique a privilegier pour la suite.

Un etat genere contient une provenance inductive depuis la racine. Chaque enfant ajoute une decision sur une variable fraiche. La profondeur est derivee du witness de generation.

Cette couche fournit deja :

~~~text
racine generee
enfants frais
historique structurel
continuations respectant l'historique
acceptation SAT separee
split genere exact
preservation de viabilite
frontieres heterogenes de contextes issus de profondeurs differentes
~~~

La relation globale de flip entre parents differents existe encore dans l'ancien noyau. Elle n'est pas encore migree dans le systeme durci.

### 7.1 Point conceptuel central

La reduction de frontiere n'est pas le centre de la methode.

Le centre est :

> le calcul constitue progressivement des determinations qui modifient les relations reconstructibles entre continuations.

La cible dynamique est donc :

~~~text
H_k
-> nouvelle determination
-> H_(k+1)
-> nouvel espace de relations reconstructibles
-> nouveaux transports possibles
-> eventuelle reduction de frontiere
~~~

La reduction est une consequence locale de cette constitution.

La provenance n'est donc pas seulement une memoire ou un journal. Elle doit pouvoir intervenir dans la definition meme de ce qui devient calculable ensuite.

La cible formelle future doit permettre :

~~~text
RelationSearch H_k A B = none
~~~

puis, apres constitution d'une nouvelle determination :

~~~text
RelationSearch H_(k+1) A' B' = some transport
~~~

sans interpreter cela comme la simple exploration plus longue d'un graphe relationnel fixe.

C'est le test direct de la proposition :

~~~text
le chemin est le calcul
~~~

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

Cette section est un audit externe, pas une definition du programme. Une ressemblance locale avec une notion connue ne justifie ni reduction conceptuelle ni identification de l'architecture. Le programme doit d'abord etre caracterise par ses propres invariants constitutifs, puis compare aux cadres existants.

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
  SearchSystem.lean
  AcceptingTransport.lean
  AcceptedSplit.lean
  AcceptedFrontier.lean
  AcceptedFrontierPreservation.lean
  AcceptedRelationalTransport.lean
  AcceptedFrontierNormalization.lean
  ConstitutiveState.lean
  FrontierTrajectory.lean
  DynamicRelationSearch.lean
  TransportCode.lean
  TransportClosure.lean
  FrontierReduction.lean
  RelationalTransport.lean
  IrreducibleFrontier.lean
  ConstitutiveWidth.lean
  FiniteFrontierNormalization.lean
  FrontierPreservation.lean

ConstitutiveSearch/SAT/
  ConstraintTransport.lean
  AcceptedSAT.lean
  AcceptedBinaryBranch.lean
  StructuralBranchContext.lean
  GeneratedStructuralContext.lean
  StructuralGlobalContextRelation.lean
  StructuralDynamicRelation.lean
  BinaryBranch.lean
  RestrictionTransport.lean
  ResidualFlipTransport.lean
  ResidualTrajectory.lean
  BranchContext.lean
  BranchContextTransport.lean
  GeneratedContext.lean
  GlobalContextRelation.lean
~~~

Les couches nouvelles etablissent maintenant :

~~~text
relation executable -> transport total preservant Accept
normalisation automatique -> preservation de FrontierViable
flip global durci -> comparaison de contextes de parents differents
ConstitutiveState -> frontiere + information constituee distincte
FrontierTrajectory -> composition proof-relevant des etapes
widthTrace -> largeur derivee du chemin effectivement construit
DynamicRelationSearch -> relation et recherche indexees par l'etat constitue
GeneratedSplitAnchor -> information dynamique issue d'un split SAT certifie
TransportCode -> syntaxe finie des transports primitifs et de leur composition
TransportClosure -> fermeture compositionnelle explicite, distincte de sa recherche
~~~

### 22.2 Prochains modules prioritaires

Les noms restent provisoires.

~~~text
ConstitutiveSearch/
  StructuralProgress.lean
  ClosureSearch.lean
  ComplexityInterface.lean

ConstitutiveSearch/SAT/
  StructuralContextTrajectory.lean
  SimplifiedRestriction.lean
  RenamingTransport.lean
  SubstitutionTransport.lean
  PropagationTransport.lean
  ParametricSymmetricFamily.lean
  WidthSeparators.lean
~~~

Le prochain verrou principal est la progression structurelle :

~~~text
decision fraiche
-> historique sans repetition
-> variables choisies prises dans une ressource finie pertinente
-> profondeur bornee par cette ressource
~~~

Cette borne doit etre derivee de la structure des decisions. Elle ne doit pas etre
postulee par un compteur externe.

La recherche exhaustive dans TransportClosure reste egalement ouverte. La
fermeture existe comme syntaxe finie et les codes s'interpretent correctement,
mais aucun oracle de recherche de code n'est suppose.

## 23. Statut des phases

~~~text
[FAIT] noyau directionnel historique sur Completion
[FAIT] frontieres proof-relevant historiques
[FAIT] recherche relationnelle directe historique
[FAIT] normalisation finie historique
[FAIT] preservation historique dans les deux sens
[FAIT] relation globale de flip entre parents differents dans l'ancien noyau

[FAIT] SearchSystem
[FAIT] separation Continuation / Accept
[FAIT] Viable derive
[FAIT] transport total preservant Accept
[FAIT] split exact durci
[FAIT] frontier semantics durcie
[FAIT] SAT structurel et provenance generee

[FAIT P1] moteur relationnel automatique durci
[FAIT P1] normalisation preservant FrontierViable
[FAIT P1] flip global durci entre parents differents

[FAIT P2] ConstitutiveState
[FAIT P2] FrontierTrajectory
[FAIT P2] trajectoire SAT a deux niveaux
[FAIT P2] trace [1, 2, 1, 2, 1] et Viable preserve

[FAIT P3a] relation indexee par ConstitutiveState
[FAIT P3a] meme frontiere, none avant constitution, some apres
[FAIT P3a] largeur 2 -> 1 par changement de constitution seulement

[FAIT P3b] GeneratedSplitAnchor issu d'un split SAT certifie
[FAIT P3b] relation SAT absente avant enregistrement du split
[FAIT P3b] relation SAT presente apres constitution du certificat
[FAIT P3b] trajectoire [1, 2, 2, 1] avec Viable preserve

[FAIT P4a] TransportCode fini
[FAIT P4a] interpretation acceptance-preserving des codes
[FAIT P4a] fermeture compositionnelle libre
[FAIT P4a] separateur direct width 2 / compose width 1
[FAIT P4a] code compose explicite de taille 2

[P4b] recherche executable generale dans les codes de fermeture
[P4b] cout et bornes de cette recherche

[P5] historique de variables sans repetition
[P5] variables de decision pertinentes
[P5] borne de profondeur derivee de la ressource finie
[P5] terminalite structurelle

[P6] familles parametriques positives
[P6] familles separatrices et bornes de largeur

[P7] tailles et couts
[P7] theorem conditionnel de complexite

[P8] audit externe de nouveaute et de comparaison

[FERME] toute revendication P/NP avant fermeture des phases restantes
~~~

## 24. Sequence d'implementation immediate

Ordre recommande a partir du head actuel :

~~~text
1. prouver que la provenance generee ne repete aucune variable choisie fraiche
2. definir explicitement les variables pertinentes d'une instance SAT
3. renforcer la generation pour exiger que chaque variable choisie soit pertinente
4. deriver une borne de profondeur depuis cette ressource finie
5. caracteriser un etat terminal par epuisement des variables pertinentes
6. verifier cette progression sur la trajectoire SAT constitutive
7. construire ensuite une famille SAT parametrique avec largeur controlee
8. construire en parallele une famille separatrice ou la largeur croit
9. definir une recherche bornee de TransportCode sans en faire un oracle
10. mesurer taille des codes, cout de recherche, cout de normalisation et taille d'etat
11. assembler le theorem conditionnel de complexite
~~~

Le verrou courant est donc :

> obtenir la borne de longueur du chemin depuis les determinations structurelles
> elles-memes, et non depuis une limite d'iterations posee a l'exterieur.

La fermeture compositionnelle est disponible comme objet mathematique fini. Sa
recherche algorithmique reste un cout a analyser, pas une primitive gratuite.

## 25. Prochain theorem global vise

Forme cible :

> Pour toute trajectoire finie construite par splits structurels exacts, constitutions d'etat et absorptions certifiees par des transports preservant l'acceptation, la viabilite de la frontiere initiale est equivalente a la viabilite de la frontiere finale.

Forme conceptuelle :

~~~text
ViableFrontier F0 <-> ViableFrontier Fn
~~~

sans exiger que les transports d'absorption soient inversibles.

La trajectoire doit egalement enregistrer assez de provenance pour permettre de calculer quelles relations sont disponibles a chaque etape.

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
Continuation structurelle / Accept
-> transport total preserve Accept
-> frontiere viable
-> moteur relationnel automatique
-> normalisation automatique
-> contexte SAT genere et proof-relevant
-> relation globale entre parents differents
-> ConstitutiveState
-> FrontierTrajectory
-> relations dont la disponibilite depend du chemin
-> certificat dynamique issu d'un vrai split SAT
-> TransportCode fini
-> fermeture compositionnelle explicite
~~~

Deux separateurs structurants sont maintenant formalises.

Premier separateur, constitution dynamique :

~~~text
meme frontiere
none avant constitution
some transport apres constitution
largeur 2 -> 1
~~~

La version SAT remplace l'ancre abstraite par un certificat contenant un parent
genere, une variable fraiche et les enfants exacts du split certifie.

Deuxieme separateur, composition :

~~~text
recherche directe A -> C = none
A -> B existe
B -> C existe
code A -> B -> C de taille 2
largeur directe [A,C] = 2
largeur avec recherche du code compose = 1
~~~

Cela etablit formellement que "irreductible pour la recherche directe" et
"irreductible sous composition" sont deux proprietes differentes.

Le prochain obstacle n'est plus la semantique du chemin ni l'existence de la
composition. Il est la progression globale :

~~~text
combien de determinations fraiches peuvent etre constituees
avant que la ressource structurelle finie soit epuisee ?
~~~

Puis seulement viendront les bornes parametriques de largeur et le calcul de
complexite totale.

Les comparaisons externes restent des audits de nouveaute. Elles ne definissent
pas le mecanisme constitutif.
