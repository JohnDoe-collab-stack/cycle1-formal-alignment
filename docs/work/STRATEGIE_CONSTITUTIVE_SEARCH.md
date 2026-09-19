# Strategie auditee - NP AND/OR P et recherche constitutive par trajectoire

## Statut du document

Ce document est le plan scientifique de travail de la branche research/np-and-or-p.

Base scientifique de cloture avant cette mise a jour documentaire :

~~~text
7270966eed7177236ba4db28051dae1d2613eaba
~~~

Le programme NP AND/OR P est maintenant formellement clos au perimetre annonce. Les obligations de composabilite du schedule, de synthese quantitative et de non-factorisation sous oubli de constitution sont fermees. Le pont classique minimal vers des interfaces Nat-codees de probleme de decision, P et NP est egalement formalise. Le theorem npAndPObjectiveComplete constitue le marqueur d'arret de l'objectif NP / P. Il n'enonce ni P = NP ni P != NP.

P1 a P6c et les couches quantitatives P7a a P7d-f sont maintenant formalises au niveau annonce dans ce document. Le head code ci-dessus a passe Linux et Windows. Le normaliseur generique possede une borne quadratique de controle-flow en largeur, la fermeture compositionnelle possede des lois de croissance explicites et des regimes polynomiaux prouves pour tout fuel fixe ainsi que pour tout fuel variable uniformement borne. Les longueurs de listes de candidats peuvent elles-memes croitre polynomialement avec la taille d'entree. Les profils constitutifs multidimensionnels se composent generiquement, deux familles SAT parametriques distinctes sont instanciees dans l'interface input-polynomiale, et le passage vers un cout machine polynomial est formalise uniquement sous un RepresentationMachineBridge explicite. Le CI final du head documentaire doit confirmer de nouveau l'ensemble apres synchronisation du plan.

La consolidation GitHub est terminee : le chantier NP AND/OR P n'a plus qu'une branche canonique, research/np-and-or-p.

Le document est un document de chantier. Il ne constitue aucune revendication de classe de complexite generale. Sa fonction est de distinguer exactement :

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
ConstitutiveSearch/AcceptedFrontierNormalization.lean
ConstitutiveSearch/AcceptedFrontierNormalizationCosts.lean

ConstitutiveSearch/ConstitutiveState.lean
ConstitutiveSearch/FrontierTrajectory.lean
ConstitutiveSearch/DynamicRelationSearch.lean
ConstitutiveSearch/TransportCode.lean
ConstitutiveSearch/TransportClosure.lean
ConstitutiveSearch/ClosureSearch.lean
ConstitutiveSearch/ClosureSearchCosts.lean
ConstitutiveSearch/ClosureSearchGrowth.lean
ConstitutiveSearch/ClosureSearchPolynomialRegimes.lean
ConstitutiveSearch/ClosureSearchPolynomialComplexity.lean
ConstitutiveSearch/ClosureSearchFixedFuelPolynomial.lean
ConstitutiveSearch/ClosureSearchGrowingFuelSeparator.lean
ConstitutiveSearch/PolynomialExponentialSeparator.lean
ConstitutiveSearch/ClosureSearchLogFuelPolynomial.lean
ConstitutiveSearch/ClosureSearchScaledLogFuelPolynomial.lean
ConstitutiveSearch/ClosureSearchBoundedCandidatesLogFuelPolynomial.lean
ConstitutiveSearch/ClosureSearchJointGrowthPolynomial.lean
ConstitutiveSearch/ClosureSearchWidthControlled.lean
ConstitutiveSearch/ClosureSearchWidthGrowthPolynomial.lean
ConstitutiveSearch/ClosureSearchJointGrowthSeparator.lean

ConstitutiveSearch/ComplexityInterface.lean
ConstitutiveSearch/RepresentationCost.lean
ConstitutiveSearch/MachineCostInterface.lean
ConstitutiveSearch/MachineCostPolynomial.lean
ConstitutiveSearch/ConstitutiveComplexityProfile.lean
ConstitutiveSearch/ConstitutiveComplexityComposition.lean
ConstitutiveSearch/PolynomialCostEnvelope.lean
ConstitutiveSearch/ConstitutiveComplexityPolynomial.lean
ConstitutiveSearch/ConstitutiveComplexityInputPolynomial.lean

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
ConstitutiveSearch/SAT/StructuralGlobalContextRelation.lean
ConstitutiveSearch/SAT/StructuralDynamicRelation.lean
ConstitutiveSearch/SAT/StructuralProgress.lean

ConstitutiveSearch/SAT/ParametricSymmetricFamily.lean
ConstitutiveSearch/SAT/ParametricSymmetricTrajectory.lean
ConstitutiveSearch/SAT/ExplicitStackedSymmetricFamily.lean
ConstitutiveSearch/SAT/ExplicitFamilyResources.lean
ConstitutiveSearch/SAT/ExplicitFamilyCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyProvenance.lean
ConstitutiveSearch/SAT/ExplicitFamilyTransportCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyRelationCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyNormalizationCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyComplexity.lean
ConstitutiveSearch/SAT/ExplicitFamilyBitCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyEqualityCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyBitComplexity.lean
ConstitutiveSearch/SAT/ExplicitFamilyPolynomialCosts.lean
ConstitutiveSearch/SAT/ExplicitFamilyInputComplexity.lean
ConstitutiveSearch/SAT/ExplicitFamilyConstitutiveProfile.lean
ConstitutiveSearch/SAT/ExplicitFamilyCostPolynomials.lean
ConstitutiveSearch/SAT/ExplicitFamilyInputPolynomialProfile.lean
ConstitutiveSearch/SAT/ExplicitFamilyMachineComplexity.lean
ConstitutiveSearch/SAT/ExplicitFamilyMachinePolynomial.lean

ConstitutiveSearch/SAT/ParametricComposedFamily.lean
ConstitutiveSearch/SAT/ParametricComposedClosure.lean
ConstitutiveSearch/SAT/ParametricComposedWidth.lean
ConstitutiveSearch/SAT/ParametricComposedComplexity.lean
ConstitutiveSearch/SAT/ParametricComposedBitComplexity.lean
ConstitutiveSearch/SAT/ParametricComposedPolynomialCosts.lean
ConstitutiveSearch/SAT/ParametricComposedWidthControlled.lean
ConstitutiveSearch/SAT/TrajectoryDerivedClosure.lean
ConstitutiveSearch/SAT/TrajectoryDerivedClosureComplexity.lean
ConstitutiveSearch/SAT/SequentialGlobalClosureSeparator.lean
ConstitutiveSearch/SAT/TrajectoryDerivedSequentialExecution.lean
ConstitutiveSearch/SAT/WidthSeparators.lean
ConstitutiveSearch/SAT/WidthSeparatorConstitutiveProfile.lean

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

Le projet dispose maintenant d'une architecture constructive et quantitative dans laquelle :

~~~text
des espaces proof-relevant sont indexes par des etats
des splits produisent plusieurs branches
des relations structurelles produisent des transports directionnels
des branches transportables peuvent etre absorbees
une normalisation finie construit une frontiere irreductible
la provenance des survivants permet un retour vers la frontiere source
des branches SAT recursives conservent leur historique
des relations durcies comparent des branches de parents differents
la disponibilite relationnelle peut changer avec l'etat constitue
des transports primitifs peuvent etre fermes par composition finie
le normaliseur generique a pairClassifications <= width^2
et findCalls <= 2 * width^2
la recherche de fermeture expose ses compteurs et ses lois de croissance
F(n) et la phase SAT composee ont des charges binaires et des enveloppes
polynomiales indexees par la taille concrete de l'entree
un ConstitutiveComplexityProfile conserve separement entree, profondeur,
largeur, vecteur d'evenements et charge de representation
les profils se composent sequentiellement sans perdre leurs dimensions
toute famille de profils input-polynomiale reste telle par composition
pour tout fuel fixe, ClosureSearch est polynomial dans un nombre de candidats polynomial
un fuel variable uniformement borne par une constante conserve ce regime polynomial
le separateur de largeur constitue une deuxieme famille parametrique input-polynomiale
un cout machine polynomial ne suit qu'apres un RepresentationMachineBridge explicite
le theorem abstrait profil -> cout machine polynomial est ferme sous ce bridge
~~~

### 4.2 Ce qui n'est pas etabli

Le projet ne montre pas actuellement :

~~~text
que SAT general a petite largeur
que la largeur actuelle est intrinsique
que les transports annonces sont complets pour SAT general
que la fermeture compositionnelle bornee explore toute la fermeture mathematique
qu'un fuel dont la borne croit avec la taille d'entree conserve un cout polynomial pour le moteur ClosureSearch actuel
que les tailles d'etats, certificats et provenances restent polynomiales
pour toute famille SAT
que la profondeur globale est polynomialement bornee pour SAT general
que les exemples de flip couvrent SAT arbitraire
qu'un RepresentationMachineBridge concret est deja prouve pour un runtime donne
qu'une consequence generale de classe de complexite est etablie
~~~

Les bornes polynomiales actuellement obtenues sont des theoremes sur les familles
et les regimes explicitement formalises. Elles ne doivent pas etre extrapolees
a SAT general sans hypotheses et preuves supplementaires.

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

La relation globale de flip entre parents differents existe maintenant aussi dans le systeme durci via StructuralGlobalContextRelation. Elle agit sur toutes les continuations structurelles, tandis que la preservation de satisfaction est prouvee separement. StructuralDynamicRelation ajoute en outre une relation indexee par l'etat constitue, de sorte que la meme frontiere peut etre non reliee avant constitution d'un certificat puis reliee apres constitution.

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

Formalisee.

Le projet distingue maintenant explicitement :

~~~text
largeur directe sous le moteur primitif annonce
!=
largeur obtenue apres recherche dans la fermeture compositionnelle
~~~

Sur la famille SAT parametrique composee :

~~~text
frontiere directe [source,target]
SearchIrreducible sous composedPrimitiveSearch
largeur directe = 2

source -> middle -> target
code compose de taille 2
ClosureSearch avec fuel 2 retrouve le code
reduction acceptance-preserving
largeur fermee = 1
Viable paire <-> Viable singleton
~~~

Ce resultat est relatif aux generateurs et au budget de fermeture annonces. Il ne doit pas etre interprete comme une largeur intrinseque de SAT.

### 8.4 Largeur minimale certifiable

A envisager seulement comme mesure mathematique secondaire.

Elle ne doit pas devenir une primitive algorithmique, car sa recherche peut elle-meme etre difficile.

---

## 9. P1 ferme : trajectoires completes de frontieres

FrontierTrajectory fait maintenant du chemin un objet proof-relevant du calcul.

Un ConstitutiveStep contient :

~~~text
frontiere source
frontiere cible
preservation exacte de FrontierViable
transition de constitution
~~~

Les pas se composent en trajectoires finies. Le noyau derive :

~~~text
Viable F_0 <-> Viable F_n
length
widthTrace
maxWidth
~~~

sans utiliser la largeur pour piloter retroactivement la trajectoire.

La couche SAT fournit des trajectoires multi-niveaux, puis la famille fermee
F(n) produit automatiquement une trajectoire certifiee de longueur n avec :

~~~text
length(widthTrace) = 2n + 1
W(n) <= 2
Viable racine <-> Viable endpoint
~~~

La trajectoire et sa largeur sont donc des objets construits et mesures apres constitution.

## 10. P2 ferme : codes, fermeture et recherche compositionnelle

Le projet possede maintenant une syntaxe finie TransportCode avec interpretation
acceptance-preserving et taille explicite.

TransportClosure distingue :

~~~text
existence d'un code compose
recherche executable de ce code
cout de la recherche
~~~

ClosureSearch effectue une recherche bornee par :

~~~text
liste finie de candidats
fuel de composition
~~~

et enregistre :

~~~text
primitiveQueries
compositionCandidates
~~~

ClosureSearchCosts et ClosureSearchGrowth donnent des budgets generiques ainsi
que leurs lois exactes de croissance.

Le separateur direct/compose est ferme abstraitement puis sur une famille SAT
parametrique : la recherche directe source -> target echoue, tandis que deux
relations primitives via un etat intermediaire donnent un code compose de taille
2 retrouve par la recherche bornee.

Les regimes quantitatifs maintenant prouves sont :

~~~text
fuel fixe arbitraire
+ candidateCount polynomial en inputBits
=> primitiveQueries polynomial
=> compositionCandidates polynomial

fuel variable
+ borne uniforme fuel <= fuelCap constant
+ candidateCount polynomial en inputBits
=> memes conclusions
~~~

Le cas encore ouvert est celui ou la borne de fuel elle-meme croit avec l'entree.

## 11. P3 ferme : ancres dynamiques

Le test "le chemin est le calcul" est maintenant formalise generiquement et sur
SAT.

Le noyau dynamique permet au type des relations reconstructibles de dependre de
l'etat constitue courant.

Le separateur generique etablit :

~~~text
meme frontiere [left,right]
constitution avant = sans ancre
relation left -> right absente
largeur = 2

meme frontiere [left,right]
constitution apres = ancre acquise
relation left -> right presente
largeur = 1
~~~

La version SAT remplace l'ancre abstraite par GeneratedSplitAnchor, constitue
depuis un parent genere, une variable fraiche et le split exact correspondant.

Ainsi la relation n'est pas activee par un drapeau semantique externe : elle est
reconstruite a partir d'une determination effectivement constituee par le chemin.

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

## 13. P4 ferme : progression structurelle et terminalite

StructuralProgress derive la progression depuis une ressource syntaxique finie,
sans compteur de terminaison externe.

La couche formalise :

~~~text
historique de variables sans repetition
decision sur variable fraiche
ResourceDecision
ResourceTerminal
depth + remaining.length = initial.length
depth <= initial.length
remaining = [] -> terminalite structurelle
~~~

Sur F(n), la ressource exacte contient n variables de decision, est consommee
jusqu'a la liste vide, et l'endpoint satisfait :

~~~text
depth = n
terminal
~~~

La borne de profondeur est donc reconstruite depuis la ressource de l'instance
dans cette famille, et non postulee par un horizon externe.

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
  ClosureSearch.lean
  ClosureSearchCosts.lean
  ComplexityInterface.lean
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
  StructuralProgress.lean
  ParametricSymmetricFamily.lean
  ParametricSymmetricTrajectory.lean
  ExplicitStackedSymmetricFamily.lean
  ExplicitFamilyResources.lean
  ExplicitFamilyCosts.lean
  ExplicitFamilyProvenance.lean
  ExplicitFamilyTransportCosts.lean
  ExplicitFamilyRelationCosts.lean
  ExplicitFamilyNormalizationCosts.lean
  ExplicitFamilyComplexity.lean
  WidthSeparators.lean
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
TransportClosure -> fermeture compositionnelle explicite
ClosureSearch -> recherche executable bornee par fuel et liste finie de candidats
ClosureSearchCosts -> bornes recursives des requetes primitives et candidats de composition
ComplexityInterface -> separation comptes certifies / couts atomiques / cout agrege conditionnel
StructuralProgress -> ressource syntaxique finie, histoire sans repetition et terminalite
ParametricSymmetricFamily -> famille SAT locale de taille arbitraire avec reduction sibling a largeur 1
ParametricSymmetricTrajectory -> trajectoire flip-symetrique arbitrairement longue avec W(n) <= 2
ExplicitStackedSymmetricFamily -> F(n) ferme, 2n clauses, trajectoire automatique de longueur n
ExplicitFamilyResources -> ressource exacte n, endpoint depth n et terminalite
ExplicitFamilyCosts -> comptages structurels exacts et proxy de travail etroit 4n+1
ExplicitFamilyProvenance -> taille de provenance exactement egale a la profondeur
ExplicitFamilyTransportCosts -> un atome TransportCode par absorption locale
ExplicitFamilyRelationCosts -> surface de verification relationnelle explicitement bornee
ExplicitFamilyNormalizationCosts -> 2n appels find et surface bidirectionnelle bornee
ExplicitFamilyComplexity -> profil de comptes F(n) + cout agrege conditionnel
WidthSeparators -> frontieres viables de largeur arbitraire irreductibles pour un flip fixe
~~~

### 22.2 Prochains modules prioritaires

Les noms restent provisoires.

~~~text
ConstitutiveSearch/
  RepresentationCost.lean

ConstitutiveSearch/SAT/
  StructuralContextTrajectory.lean
  ExplicitFamilyBitCosts.lean
  ComposedTransportFamily.lean
  SimplifiedRestriction.lean
  RenamingTransport.lean
  SubstitutionTransport.lean
  PropagationTransport.lean
~~~

La progression structurelle de base est maintenant fermee :

~~~text
decision fraiche
-> historique global sans repetition
-> consommation d'une ressource syntaxique finie
-> invariant depth + remaining = initial
-> epuisement => aucune nouvelle decision consommante
-> profondeur finale exacte en cas d'epuisement
~~~

Le noyau P5 conserve sa ressource generique par occurrences syntaxiques. Pour
la famille fermee F(n), une ressource plus precise est maintenant construite :

~~~text
explicitFamilyDecisionResource n
= [n-1, ..., 1, 0]

taille = n
~~~

Le constructeur resource-aligned consomme exactement une entree par niveau et
atteint le meme endpoint avec ressource vide. On obtient donc sur cette famille :

~~~text
depth(endpoint) = n
ResourceTerminal endpoint []
aucune decision resource-consuming supplementaire
~~~

Cette ressource est specifique a la strategie annoncee pour F(n) ; elle ne doit
pas etre interpretee comme une caracterisation generale des variables
pertinentes de SAT.

Le theorem multi-niveaux et son instanciation fermee sont maintenant disponibles.

La couche abstraite etablit :

~~~text
pour toute FlipSymmetricTrajectory de longueur n
chaque split est certifie frais et flip-symetrique
chaque paire sibling est reduite a un singleton
la viabilite des singletons initial/final est equivalente
toute largeur observee vaut 1 ou 2
donc W(n) <= 2 independamment de n
~~~

La couche fermee definit ensuite :

~~~text
F(n) = explicitStackedSymmetricFamily n
~~~

avec exactement 2n clauses. Les variables de decision sont n-1, ..., 0 et la
variable n sert d'ancre commune. Le constructeur `explicitStackedTrajectory n`
part directement de la racine de F(n) et produit une
`FlipSymmetricTrajectory` indexee par la longueur n.

Comme le residuel SAT actuel est le residuel faible, une decision vraie conserve
la clause negative sibling. Le constructeur ne masque pas ce fait : il maintient
explicitement un prefixe de clauses retenues et prouve que les variables futures
l'evitent.

On obtient pour tout n :

~~~text
nombre de clauses de F(n) = 2n
Cnf.literalCount(F(n)) = 4n
taille de la ressource exacte de decision = n
longueur de la trajectoire certifiee = n
longueur de widthTrace = 2n + 1
frontierSlotCount = 3n + 1
toute largeur observee <= 2
depth(endpoint) = n
endpoint structurellement terminal
Viable [root(F(n))] <-> Viable [endpoint(n)]
~~~

Un proxy etroit de travail structurel est egalement defini :

~~~text
structuralWorkUnits
= stepCount + frontierSlotCount
= 4n + 1
~~~

Cette quantite n'est pas un temps d'execution. Les couches ulterieures facturent
maintenant separement la recherche relationnelle, les certificats, la
representation binaire et la recherche compositionnelle. Les couts machine
restent une couche distincte, accessible uniquement sous un bridge explicite.

Les tailles de provenance et de certificats de la strategie fermee sont
maintenant explicites :

~~~text
provenanceSize(endpoint) = n
context.decisions.length(endpoint) = n
taille de chaque code local de flip = 1 atome
nombre total d'atomes de transport sur la trajectoire = n
~~~

Une surface de verification relationnelle est egalement definie. Pour une paire
sibling, elle compte les positions de litteraux des deux residuels, les decisions
des deux historiques et la variable de flip. Sur F(n), la somme est bornee par :

~~~text
n * uniformRelationVerificationUnit (4n) n
~~~

Cette borne reste une surface structurelle de verification. Elle ne doit pas
etre confondue avec un temps machine. La couche quantitative suivante reconnecte
cependant F(n) au moteur generique : generatedStructuralFlipAtSearch retrouve le
witness sibling certifie, les classifications bidirectionnelles comptent
exactement 2n appels find sur la trajectoire explicite, et le normaliseur
generique arbitraire possede maintenant les bornes :

~~~text
pairClassifications <= width^2
findCalls <= 2 * width^2
~~~

Ces bornes comptent le controle-flow. Les couts binaires des objets inspectes
sont traites dans la couche de representation, et leur traduction en cout
machine reste soumise a un RepresentationMachineBridge explicite.

Une recherche executable bornee dans TransportClosure existe maintenant :

~~~text
searchTransportClosureBounded
  primitiveSearch
  candidates
  fuel
  source
  target
~~~

Elle tente d'abord une relation primitive puis explore des etats intermediaires
dans une liste finie de candidats. Son run expose explicitement :

~~~text
primitiveQueries
compositionCandidates
~~~

La regression canonique distingue fuel 1 et fuel 2 : le chemin compose A -> B
-> C n'est pas trouve avec fuel 1, est trouve avec fuel 2, produit un code de
taille 2, effectue 3 requetes primitives et teste 1 candidat de composition.
Le moteur borne peut ensuite etre injecte dans normalizeWithTransportClosure et
reduire la paire a largeur 1.

Les compteurs possedent maintenant des bornes recursives generales :

~~~text
closurePrimitiveQueryBudget candidateCount fuel
closureCompositionCandidateBudget candidateCount fuel
~~~

et les theoremes correspondants prouvent que les compteurs reels du moteur
borne restent sous ces budgets pour toute source, toute cible, toute liste
finie de candidats et tout fuel. ClosureSearchGrowth ferme en plus plusieurs
lois exactes :

~~~text
viaPrimitiveQueryBudget r m = m * (r + r)
viaCompositionCandidateBudget r m = m * (r + r + 1)
candidateCount = 1 :
  B(0) = 0
  B(f+1) = 2 * B(f) + 1
fuel = 2 :
  primitiveQueriesBudget = 2m + 1
  compositionCandidatesBudget = m(2m + 1)
~~~

Ces lois exposent explicitement les regimes ou le fuel ou le nombre de candidats
peuvent provoquer une croissance rapide. Elles n'imposent aucune borne
polynomiale uniforme a priori.

Cette recherche reste volontairement incomplete relativement a une fermeture
mathematique non bornee : none signifie uniquement absence de code dans le fuel
et la liste de candidats annonces.

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

[FAIT P4b-a] recherche executable bornee dans TransportClosure
[FAIT P4b-a] fuel explicite et liste finie de candidats
[FAIT P4b-a] compteurs primitiveQueries et compositionCandidates
[FAIT P4b-a] separateur fuel 1 / fuel 2
[FAIT P4b-a] code compose retrouve puis utilise par le normaliseur
[QUALIFICATION P4b-a] none reste relatif au budget de recherche

[FAIT P4b-b] budgets recursifs primitiveQueries / compositionCandidates
[FAIT P4b-b] bornes generales pour tout fuel et toute liste finie de candidats
[FAIT P4b-b] regression candidateCount=1, fuel=1/2
[QUALIFICATION P4b-b] les budgets exposent la croissance de l'arbre de recherche, sans promesse polynomiale
[FAIT P4b-b] viaPrimitiveQueryBudget r m = m * (r + r)
[FAIT P4b-b] viaCompositionCandidateBudget r m = m * (r + r + 1)
[FAIT P4b-b] candidateCount=1 : primitive et composition suivent B(0)=0, B(f+1)=2B(f)+1
[FAIT P4b-b] regression fuel=4 : budgets = 15
[FAIT P4b-b] fuel=2 : primitiveQueriesBudget = 2m+1
[FAIT P4b-b] fuel=2 : compositionCandidatesBudget = m(2m+1)
[QUALIFICATION P4b-b] la recurrence binaire caracterise le budget du moteur; elle n'est pas une borne inferieure de temps machine

[FAIT P4b-c] famille SAT parametrique construite au-dessus de l'endpoint de F(n)
[FAIT P4b-c] source -> target absent de la recherche primitive annoncee
[FAIT P4b-c] source -> middle et middle -> target presents
[FAIT P4b-c] fuel 1 ne trouve aucun code source -> target
[FAIT P4b-c] fuel 2 retrouve un code compose de taille 2
[FAIT P4b-c] run compose : 3 primitiveQueries et 1 compositionCandidate
[FAIT P4b-c] compteurs reels sous ClosureSearchCosts candidateCount=1, fuel=2
[FAIT P4b-c] paire directe SearchIrreducible de largeur 2
[FAIT P4b-c] reduction closure acceptance-preserving de largeur 1
[FAIT P4b-c] Viable paire <-> Viable singleton apres reduction composee
[QUALIFICATION P4b-c] separateur de l'interface primitive/composee, pas revendication de durete SAT intrinseque

[FAIT P5] historique de variables sans repetition
[FAIT P5] decision liee a une occurrence de ressource syntaxique finie
[FAIT P5] borne de profondeur derivee de la ressource finie
[FAIT P5] terminalite structurelle par epuisement
[FAIT P5] invariant exact depth + remaining = initial

[FAIT P6a] famille SAT symetrique sur background arbitraire
[FAIT P6a] residuals siblings relies par flip structurel
[FAIT P6a] reduction certifiee sibling width = 1
[FAIT P6a] preservation de Viable sans requete SAT

[FAIT P6b] FlipSymmetricTrajectory de longueur arbitraire n
[FAIT P6b] composition expansion -> reduction -> tail
[FAIT P6b] preservation de Viable entre singleton initial et final
[FAIT P6b] toute largeur de la trace appartient a {1,2}
[FAIT P6b] borne uniforme W(n) <= 2

[FAIT P6b-explicit] F(n) = explicitStackedSymmetricFamily n
[FAIT P6b-explicit] nombre de clauses = 2n
[FAIT P6b-explicit] construction automatique d'une trajectoire de longueur n
[FAIT P6b-explicit] widthTrace de longueur 2n + 1
[FAIT P6b-explicit] borne uniforme W(n) <= 2
[FAIT P6b-explicit] preservation de Viable racine <-> endpoint
[FAIT P6b-explicit] accumulation du residuel faible suivie explicitement

[FAIT P6c] isolatedFrontier n de largeur n
[FAIT P6c] meme residuel vide mais provenances de variables distinctes
[FAIT P6c] aucun flip fixe ne relie deux enfants distincts
[FAIT P6c] SearchIrreducible pour toute largeur n sous le moteur annonce
[FAIT P6c] frontieres separatrices non vides viables
[QUALIFICATION P6c] separateur relatif au moteur de flip, pas durete intrinseque

[FAIT P7a] Cnf.literalCount(F(n)) = 4n
[FAIT P7a] ressource exacte de decision de taille n
[FAIT P7a] ressource consommee jusqu'a [] sur le meme endpoint
[FAIT P7a] depth(endpoint) = n et terminalite structurelle
[FAIT P7a] stepCount = n
[FAIT P7a] frontierSlotCount = 3n + 1
[FAIT P7a] bundle ExplicitFamilyCertifiedCounts
[FAIT P7a] proxy structurel etroit = 4n + 1

[FAIT P7b] provenanceSize(endpoint) = n
[FAIT P7b] decisions.length(endpoint) = n
[FAIT P7b] code local de flip = 1 atome
[FAIT P7b] total des atomes de transport = n
[FAIT P7b] surface de verification relationnelle bornee sur F(n)

[FAIT P7b] generatedStructuralFlipAtSearch retrouve le witness sibling certifie
[FAIT P7b] strategie fermee : exactement 2n appels find pour les classifications bidirectionnelles
[FAIT P7b] surface de verification des deux directions bornee sur F(n)
[QUALIFICATION P7b] ce comptage de controle-flow ne vaut pas cout bit-machine

[FAIT P7b] normaliseur generique : retained.length <= source.length
[FAIT P7b] insertion : au plus rest.length classifications de paires
[FAIT P7b] normalisation arbitraire : pairClassifications <= width^2
[FAIT P7b] deux find par classification, donc findCalls <= 2 * width^2
[QUALIFICATION P7b] borne de controle-flow du normaliseur, pas cout machine d'un find
[FAIT P7b] ClosureSearchCosts instancie sur une famille SAT parametrique
[FAIT P7b] fermeture composee SAT : 3 requetes primitives et 1 candidat pour le chemin a deux atomes
[FAIT P7b] charge de representation de cette fermeture instanciee et bornee polynomialement en taille d'entree
[QUALIFICATION P7b] les compteurs restent des evenements de controle-flow; leur traduction en temps machine reste distincte

[FAIT P7c-a] ComplexityCounts et AtomicCosts separes
[FAIT P7c-a] chargedCost explicite
[FAIT P7c-a] theorem conditionnel chargedCost <= uniformChargedBudget
[FAIT P7c-a] profil F(n) : 4n syntax, 3n+1 frontier, n provenance, n certificats, 2n find
[FAIT P7c-a] F(n) n'utilise aucune recherche de fermeture dans la strategie locale annoncee

[FAIT P7c-b] mesure binaire concrete de Nat, Literal, Clause, Cnf et historiques
[FAIT P7c-b] budgets binaires prouves sur F(n) et son endpoint
[FAIT P7c-b] flip preserve exactement les tailles binaires
[FAIT P7c-b] branchResidual n'augmente pas la taille binaire de la Cnf
[FAIT P7c-b] charge explicite des deux egalites structurelles du flip global
[FAIT P7c-b] AtomicCosts instancies par des charges de representation concretes

[FAIT P7c-c] explicitFamilyRepresentationBudget ferme les classes d'evenements reellement utilisees
[FAIT P7c-c] explicitFamilyRepresentationChargedCost = explicitFamilyRepresentationBudget sans hypothese atomique externe
[FAIT P7c-c] regression n=3 : cout charge = budget = 2349
[QUALIFICATION P7c-c] il s'agit d'un cout de representation, pas d'un theorem de temps machine de DecidableEq ou du runtime Lean

[FAIT P7c-d] formes polynomiales fermees des budgets formule, historique, etat et relation
[FAIT P7c-d] explicitFamilyRepresentationChargedCost <= explicitFamilyRepresentationPolynomialBudget
[FAIT P7c-d] theorem polynomial final sans axiome

[FAIT P7c-e] explicitFamilyInputBitSize = taille binaire concrete de F(n)
[FAIT P7c-e] n <= explicitFamilyInputBitSize n
[FAIT P7c-e] monotonie de l'enveloppe polynomiale
[FAIT P7c-e] cout charge <= enveloppe polynomiale indexee par la taille binaire reelle de l'entree
[QUALIFICATION P7c-e] cette borne est une complexite de representation; le cout machine concret des egalites reste une couche distincte

[FAIT P7c-f] profil separe de la phase compositionnelle : 2 slots, 2 atomes, 3 primitiveQueries, 1 compositionCandidate
[FAIT P7c-f] histories des etats du carre compose de longueur n+2
[FAIT P7c-f] tailles binaires des residuels, histories et witnesses bornees
[FAIT P7c-f] primitive query chargee par au plus deux comparaisons structurelles
[FAIT P7c-f] composedClosurePhaseRepresentationChargedCost = budget explicite
[FAIT P7c-f] budget compositionnel ferme sous forme polynomiale
[FAIT P7c-f] cout compositionnel <= enveloppe polynomiale indexee par explicitFamilyInputBitSize
[QUALIFICATION P7c-f] borne de representation de la phase ajoutee; pas un temps machine

[FAIT P7d-a] AtomicCostPointwiseLe et monotonie de chargedCost
[FAIT P7d-a] MachineCostModel separe des charges de representation
[FAIT P7d-a] affineAtomicEnvelope factor/overhead
[FAIT P7d-a] RepresentationMachineBridge comme obligation explicite
[FAIT P7d-a] borne machine agregee seulement sous bridge prouve
[QUALIFICATION P7d-a] aucun bridge vers un runtime concret n'est postule

[FAIT P7d-b] ConstitutiveComplexityProfile multidimensionnel
[FAIT P7d-b] dimensions : inputBits, depth, maxFrontierWidth, events, representationCharge
[FAIT P7d-b] ordre pointwise BoundedBy reflexif/transitif
[FAIT P7d-b] profil local F(n) instancie
[FAIT P7d-b] profil de phase compositionnelle instancie
[FAIT P7d-b] profil total local + composition instancie
[FAIT P7d-b] charge totale <= somme des enveloppes polynomiales indexees par la taille d'entree
[FAIT P7d-b] profil total : profondeur n+2, certificats n+2, 2n find directs, 3 closure queries, 1 candidat
[QUALIFICATION P7d-b] le profil conserve les dimensions; il ne les ecrase pas en une unique notion de temps

[FAIT P7d-c] cout machine total SAT separe en phase locale et phase compositionnelle
[FAIT P7d-c] budget machine calibre defini par phase
[FAIT P7d-c] theorem total machineCost <= calibratedBudget sous deux RepresentationMachineBridge explicites
[FAIT P7d-c] aucune conversion automatique representation -> machine
[QUALIFICATION P7d-c] le theorem est conditionnel; aucun runtime concret n'est postule ni certifie

[FAIT P7d-d] CostPolynomial possede une substitution interne avec theorem d'evaluation
[FAIT P7d-d] InputPolynomiallyBounded est ferme sous application d'un CostPolynomial
[FAIT P7d-d] pour tout fuel fixe, les budgets ClosureSearch sont des polynomes exacts en candidateCount
[FAIT P7d-d] candidateCount input-polynomial + fuel fixe => compteurs executables input-polynomiaux
[FAIT P7d-d] fuel variable uniformement borne par une constante + candidats input-polynomiaux => compteurs executables input-polynomiaux
[FAIT P7d-d] fuel(input)=input avec un candidat suit exactement une echelle binaire de doublement
[FAIT P7d-d] forme fermee de ce separateur : budget(input) + 1 = 2^input
[FAIT P7d-d] cette famille exacte n'admet aucune borne uniforme de degre polynomial
[FAIT P7d-d] tout CostPolynomial fini est battu par 2^n sur un input explicite construit depuis sa syntaxe
[FAIT P7d-d] 2^n n'est pas PolynomiallyBounded dans l'interface interne
[FAIT P7d-d] avec un candidat et fuel(input)=input, primitiveQueries et compositionCandidates ne sont pas PolynomiallyBounded
[FAIT P7d-d] avec un candidat et fuel <= log2(inputBits), les deux compteurs sont bornes lineairement par inputBits
[FAIT P7d-d] avec un candidat et fuel <= c*log2(inputBits), les deux compteurs ont l'enveloppe interne explicite X^c
[FAIT P7d-d] famille temoin inputBits(n)=2^n, fuel(n)=c*n : budget(n)+1 = inputBits(n)^c
[FAIT P7d-d] pour c>0 cette famille de fuel est non bornee tout en restant input-polynomiale
[FAIT P7d-d] avec candidateCount <= M constant et fuel <= c*log2(inputBits), les budgets et compteurs executables sont input-polynomiaux
[FAIT P7d-d] critere conjoint : (log2(2*candidateCount+2)+1)*fuel <= d*log2(inputBits) => budgets <= inputBits^d
[FAIT P7d-d] famille temoin conjointe : candidateCount=2^n-1 et fuel=n sont tous deux non bornes mais les budgets restent lineaires dans inputBits=2^((n+2)^2)
[FAIT P7d-d] schedule de closure controle par maxFrontierWidth, avec types d'etats dependants de l'instance
[FAIT P7d-d] largeur uniformement bornee + candidats/fuel sous cette largeur => compteurs executables input-polynomiaux
[FAIT P7d-d] critere largeur croissante : bitWidth(maxFrontierWidth)*fuel <= d*log2(inputBits) suffit pour les compteurs executables
[FAIT P7d-d] temoin executable avec maxFrontierWidth et fuel tous deux non bornes mais compteurs input-polynomiaux
[FAIT P7d-d] instance SAT composee : [middle], fuel=2, tous deux certifies sous la largeur constitutive 2
[FAIT P7d-d] separateur conjoint negatif : candidateCount=inputBits et fuel=log2(inputBits) donnent des budgets primitifs et compositionnels non InputPolynomiallyBounded
[FAIT P7d-d] TrajectoryDerivedClosure reconstruit decisionVars, splitCandidates et closureFuel depuis la trajectoire proof-relevant elle-meme
[FAIT P7d-d] sur F(n) : candidats derives = 2n et fuel derive = n
[FAIT P7d-d] la taille binaire reelle de F(n) est bornee par le CostPolynomial explicite de formule
[FAIT P7d-d] les deux budgets recursifs canoniques du schedule global derive 2n/n ne sont pas InputPolynomiallyBounded dans explicitFamilyInputBitSize
[FAIT P7d-d] separateur sequential/global : la meme trajectoire F(n) a un profil sequential input-polynomial avec 2n find directs et zero compteur ClosureSearch, tandis que son enveloppe de fermeture globale derivee est non input-polynomiale
[FAIT P7d-d] primitive-hit short circuit : pour tout fuel positif, si primitive.find reussit alors le run ClosureSearch charge exactement 1 primitiveQuery et 0 compositionCandidate
[FAIT P7d-d] le premier sibling reel de toute FlipSymmetricTrajectory non vide satisfait ce short circuit dans la closure derivee
[FAIT P7d-d] execution sequentielle derivee : en recombinant le run sibling de chaque suffixe, toute trajectoire certifiee de longueur n execute exactement n primitiveQueries et 0 compositionCandidate
[FAIT P7d-d] sur F(n), ces deux compteurs executes sont InputPolynomiallyBounded dans explicitFamilyInputBitSize
[FAIT P7d-d] PrimitiveHitPath factorise une succession executable de primitive hits, avec code de meme nombre d'atomes et execution exacte k primitiveQueries / 0 compositionCandidate
[FAIT P7d-d] tout code trouve par ClosureSearch se projette vers un PrimitiveHitPath de meme taille
[FAIT P7d-d] direct primitive miss + succes ClosureSearch => au moins un compositionCandidate inspecte et code retourne de taille >= 2
[FAIT P7d-d] tout succes ClosureSearch admet un remplacement sequentiel en primitive hits; sous direct miss ce remplacement utilise 0 compositionCandidate alors que le run global en utilise au moins un
[FAIT P7d-d] SearchableBy isole la condition locale exacte sur un TransportCode deja constitue : chaque atome doit etre retrouvable par primitive.find
[FAIT P7d-d] GlobalCompositionRequired <-> direct miss + existence d'un code SearchableBy de taille >= 2, sans executer la closure globale
[FAIT P7d-d] benchmark SAT compose : composedConstitutedCode est construit directement depuis les deux witnesses certifies, taille 2, SearchableBy, et certifie le besoin global sans recherche de closure
[FAIT P7d-d] exécution locale candidate-free : tout code SearchableBy admet une execution avec candidats=[] et fuel=1, cout exact code.size primitiveQueries / 0 compositionCandidate
[FAIT P7d-d] famille de codes SearchableBy + taille de code input-polynomiale => execution locale candidate-free input-polynomiale
[FAIT P7d-d] les familles de codes locaux sont fermees par composition : searchabilite preservee, taille additive, polynomialite locale preservee
[FAIT P7d-d] benchmark SAT compose reconstruit exactement composedConstitutedCode par composition de deux familles locales de taille 1
[FAIT P7d-d] validateSearchableCode rend SearchableBy executable : succes <-> SearchableBy et nombre exact de primitive queries = code.size
[FAIT P7d-d] ConstitutedPrimitivePath compile une suite lineaire de witnesses primitifs deja constitues vers un TransportCode de meme taille, avec validation puis execution locale de bout en bout
[QUALIFICATION P7d-d] une FlipSymmetricTrajectory n'est pas elle-meme un ConstitutedPrimitivePath entre start et finish : chaque flip local relie le false sibling au true child, tandis que la trajectoire avance du parent au true child par expansion puis absorption. Identifier ces deux graphes serait une confusion constitutive.
[FAIT P7d-d] TrajectoryConstitutedLocalSchedule extrait directement de toute FlipSymmetricTrajectory un schedule proof-relevant de witnesses sibling locaux; aucun witness, candidat, fuel ou resultat de ClosureSearch n'est fourni separement
[FAIT P7d-d] ce schedule utilise exactement trajectory.decisionVars comme domaine de provenance et contient exactement un witness / un atome de transport par etape
[FAIT P7d-d] pour toute trajectoire de longueur n : production = n atomes, validation executable = n recherches de flip directes indexees par le var de l'etape, execution locale reelle = n primitiveQueries ClosureSearch et 0 compositionCandidate avec candidats=[] / fuel=1
[FAIT P7d-d] le schedule n'utilise pas une provenance finale pour executer les etapes precedentes : chaque entree conserve son propre var constitue et utilise generatedStructuralFlipAtSearch rootFormula entry.var
[FAIT P7d-d] la projection des variables du schedule est exactement trajectory.decisionVars, dans le meme ordre
[FAIT P7d-d] le nombre d'atomes produits coincide exactement avec transportCertificateAtomCount deja audite; sur F(n), production, validation et execution locale sont InputPolynomiallyBounded dans explicitFamilyInputBitSize
[FAIT P7d-d] le cout de production n'est pas recompte : les n atomes et les n unites de provenance coincident avec certificateAtoms et provenanceUnits deja presents dans explicitFamilyComplexityCounts
[FAIT P7d-d] validation et execution sont chargees comme phases distinctes : validation = n relationFindCalls directs; execution locale = n closurePrimitiveQueries / 0 closureCompositionCandidates; les deux utilisent le cout atomique du flip direct deja audite et leurs charges de representation restent bornees par un budget polynomial indexe par la taille binaire reelle de F(n)
[FAIT CLOTURE] EndpointComposable caracterise exactement quand une suite non vide de transports locaux partage les endpoints necessaires pour compiler un TransportCode endpoint-to-endpoint; la taille du code compose est exactement la longueur du schedule
[FAIT CLOTURE] pour toute FlipSymmetricTrajectory de longueur >= 2, le schedule constitue n'est pas EndpointComposable : la cible du premier flip sibling est a profondeur d+1 tandis que la source du flip sibling suivant est a profondeur d+2
[FAIT CLOTURE] explicitFamilyConstitutedTotalProfile compose production, validation et execution sans recompter provenanceUnits ni certificateAtoms; les compteurs executes restent distincts des enveloppes recursives de ClosureSearch
[FAIT CLOTURE] explicitFamilyConstitutedTotalProfile est ConstitutiveProfileFamilyInputPolynomiallyBounded dans explicitFamilyInputBitSize
[FAIT CLOTURE] relation reconstructibility ne factorise pas par la projection frontier-only : meme frontiere, relation absente avant constitution du split exact, presente apres
[FAIT CLOTURE] le cout execute de recherche compositionnelle ne factorise pas par les seuls endpoints : meme source/target, execution locale constituee = 0 compositionCandidate, requete globale aplatie = 1
[FAIT CLOTURE] NPAndOrPProgramClosed regroupe composabilite exacte, schedule local, synthese quantitative et pertes par projection
[FAIT PONT CLASSIQUE] DecisionProblem est Nat-code; InP exige un decider correct a cout InputPolynomiallyBounded; InNP est relatif a une famille explicite de certificats avec taille et verification polynomialement bornees
[FAIT PONT CLASSIQUE] le role NP-like des continuations ne se projette vers InNP que sous SearchSystemPolynomialVerifier explicite; le role P-like ne se projette vers InP que sous SearchSystemPolynomialDecider explicite
[FAIT PONT CLASSIQUE] la trajectoire AND/OR preserve la decision extensionnelle par viable_iff, tandis que ConstitutiveProjectionLossClosed enregistre ce que la projection classique oublie
[FERME] npAndPObjectiveComplete : OBJECTIF NP / P TERMINE
[QUALIFICATION P7d-d] les separateurs negatifs portent sur les budgets recursifs canoniques, qui sont des majorants; ils ne sont pas des bornes inferieures des compteurs executes. La fermeture locale montre que la recherche globale n'est pas necessaire lorsqu'un code searchable est deja constitue. Le cout de production/validation de ce code reste une obligation distincte a expliciter.

[FAIT P7d-e] isolatedFrontier est profile par la serialization concrete de toute sa frontiere
[FAIT P7d-e] count <= isolatedFrontierInputBitSize count
[FAIT P7d-e] comptes, couts atomiques et charge de representation du separateur sont input-polynomiaux
[FAIT P7d-e] isolatedSeparatorEnvelopeProfile est input-polynomial dans toutes ses dimensions
[FAIT P7d-e] deuxieme famille parametrique independante testee dans l'interface de profils
[QUALIFICATION P7d-e] ce separateur reste relatif au moteur de flip annonce

[FAIT P7d-f] theorem abstrait profil constitutif polynomial + couts atomiques polynomiaux + bridge => cout machine polynomial
[FAIT P7d-f] composition sequentielle de deux phases preserve un cout machine total polynomial sous bridges distincts
[FAIT P7d-f] regression generique du theorem abstrait
[QUALIFICATION P7d-f] aucun RepresentationMachineBridge vers un runtime concret n'est postule

[P8] audit externe de nouveaute et de comparaison

[FERME] toute revendication generale de classe de complexite avant fermeture des phases restantes
~~~

## 24. Cloture formelle du programme

Les obligations scientifiques internes de cloture sont maintenant fermees.

~~~text
1. schedule constitue
   EndpointComposable
   -> composition endpoint-to-endpoint exactement sous egalite des endpoints
   -> FlipSymmetricTrajectory de longueur >= 2 reste un schedule local de reductions sibling

2. synthese quantitative
   trajectoire constituee
   -> schedule endogene
   -> production deja chargee dans certificateAtoms / provenanceUnits
   -> validation executable
   -> execution locale reelle
   -> profil total sans double comptage
   -> borne input-polynomiale

3. non-factorisation
   oubli de constitution / organisation temporelle
   -> perte de relation reconstructible
   -> perte d'information sur le cout execute de recherche compositionnelle
~~~

Declarations de cloture :

~~~text
NPAndOrPProgramClosed
npAndOrPProgramClosed
~~~

Le programme n'ouvre plus de nouvelle obligation scientifique interne. Sont explicitement hors objectif : SAT general, P = NP, P != NP, couverture de toute CNF, nouveaux generateurs, nouvelles familles parametriques, generalisation a tous les SearchSystem, nouveaux regimes candidateCount/fuel, regimes quasi-polynomiaux supplementaires, RepresentationMachineBridge vers un runtime concret et consequences supplementaires de classes de complexite.

Les travaux restants sont des audits du resultat ferme : audit adversarial independant et audit de litterature / positionnement.

## 25. Pont classique minimal et marqueur d'arret

Le pont final utilise volontairement des problemes de decision codes par Nat, conformement a l'interface InputPolynomiallyBounded deja presente dans le depot.

~~~text
DecisionProblem
PolynomialDecider
InP

PolynomialVerifier problem Witness
InNP problem Witness
~~~

La projection est conditionnelle et explicite :

~~~text
continuations structurelles
+ SearchSystemPolynomialVerifier
-> InNP

calcul structurel de decision
+ SearchSystemPolynomialDecider
-> InP
~~~

Aucune appartenance de classe n'est fabriquee sans le decider ou le verificateur polynomial correspondant.

Pour F(n), explicitFamilyDecisionProblem oublie schedule, provenance et organisation temporelle et ne conserve que la question extensionnelle de viabilite. explicitFamilyDecisionProjection_preserved prouve que la trajectoire constituee preserve cette decision entre racine et endpoint.

Le pont conserve la reponse oui/non et les roles classiques seulement sous leurs interfaces explicites. Il oublie des donnees dont la non-factorisation est deja prouvee : relations reconstructibles dependantes de la constitution, organisation locale versus globale, et cout execute de recherche compositionnelle.

Declarations finales :

~~~text
NPAndOrPClassicalBridgeClosed
npAndOrPClassicalBridgeClosed

NPAndPObjectiveComplete
npAndPObjectiveComplete
~~~

OBJECTIF NP / P TERMINE. STOP scientifique.

Les audits ulterieurs testent et positionnent ce resultat ferme; ils ne rouvrent pas le programme.

---
## 26. Premier theorem SAT parametrique : statut

Deux niveaux sont maintenant distingues.

### 26.1 Theorem obtenu

Pour toute `FlipSymmetricTrajectory` certifiee de longueur arbitraire `n` :

~~~text
chaque etape porte une variable fraiche
le residuel sibling est flip-symetrique
le split exact est suivi d'une absorption acceptance-preserving
Viable singleton_initial <-> Viable singleton_final
toute largeur de widthTrace vaut 1 ou 2
W(n) <= 2
~~~

La borne ne depend pas de `n`.

Ce resultat est un vrai theorem parametrique sur la longueur du chemin, pas une
regression fermee.

### 26.2 Famille fermee obtenue

La famille fermee est maintenant :

~~~text
F(n) = explicitStackedSymmetricFamily n
~~~

et le constructeur :

~~~text
explicitStackedTrajectory n
~~~

produit directement une trajectoire certifiee de longueur n depuis F(n).

Les bornes maintenant fermees sont :

~~~text
clauses(F(n)) = 2n
literalCount(F(n)) = 4n
decisionResource(F(n)).length = n
stepCount = n
length(widthTrace) = 2n + 1
frontierSlotCount = 3n + 1
W(n) <= 2
depth(endpoint) = n
endpoint terminal
Viable racine <-> Viable endpoint
~~~

Toutes ces nouvelles declarations sont auditees sans axiome.

### 26.3 Tailles de certificats et verification : statut

Les tailles suivantes sont maintenant fermees :

~~~text
provenance endpoint = n decisions
un code local de flip = 1 atome TransportCode
total des atomes utilises = n
~~~

La surface de verification directe des relations est bornee par :

~~~text
n * uniformRelationVerificationUnit (4n) n
~~~

Elle mesure les positions structurelles de formule/histoire a verifier. Elle
n'est pas un theorem de temps machine.

Le constructeur de F(n) obtient actuellement le witness local directement depuis
la symetrie certifiee. Il ne fait donc pas appel a une recherche generale
RelationSearch.find pour chaque absorption.

Les couches quantitatives correspondantes sont maintenant fermees pour les
regimes formalises :

~~~text
RelationSearch.find est compte dans les profils annonces
classifyPairCertified induit deux find et le normaliseur est borne par 2 * width^2
les tailles binaires et charges de representation sont explicites
TransportClosure possede une recherche bornee et des lois de croissance
les profils locaux, composes et separateur ont des enveloppes input-polynomiales
~~~

Restent ouverts avant toute interpretation generale de classe :

~~~text
fuel dont la borne croit avec la taille d'entree
completude des generateurs pour SAT general
bornes de largeur/profondeur/representation pour SAT general
bridge vers un modele machine concret si une revendication machine est visee
~~~

Le proxy structurel 4n+1 reste seulement un compte des niveaux certifies et des
slots de frontiere explicitement visites; il n'est pas reinterprete comme temps.

---

## 27. Theoremes separateurs : statut

Trois separateurs sont maintenant formalises.

Premier separateur semantique :

> une fonction totale entre continuations peut exister sans transport preservant l'acceptation.

Deuxieme separateur de fermeture :

> sous un moteur relationnel R annonce, une frontiere peut etre directement irreductible alors qu'un chemin de transports elementaires permet une reduction apres fermeture.

Troisieme separateur de largeur :

~~~text
isolatedFrontier n
largeur = n
meme residuel syntaxique vide pour tous les etats
provenances sur variables distinctes
SearchIrreducible sous generatedStructuralFlipAtSearch pour tout flip fixe
frontiere viable si n > 0
~~~

Le troisieme resultat est deliberement relatif au moteur annonce. Il montre que
le flip seul n'impose pas une largeur bornee, meme quand tous les residuels
syntaxiques sont identiques. Il ne constitue pas une preuve de durete
intrinseque de cette famille.

Ces resultats testent respectivement :

~~~text
la semantique du transport
la distinction direct / fermeture
la sensibilite de la largeur a la classe de relations disponible
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

La progression globale de base est maintenant fermee :

~~~text
histoire sans repetition
ressource finie consommee
depth + remaining = initial
epuisement => terminalite
~~~

Trois niveaux parametriques positifs sont maintenant formalises.

Premier niveau : un bloc SAT symetrique devant un background arbitrairement
grand se reduit a une frontiere sibling de largeur 1.

Deuxieme niveau : toute trajectoire flip-symetrique certifiee de longueur
arbitraire n preserve la viabilite de bout en bout et satisfait W(n) <= 2.

Troisieme niveau : la famille fermee F(n) est construite explicitement. Elle
contient 2n clauses et 4n litteraux, engendre automatiquement une trajectoire de
longueur n avec trace de longueur 2n+1 et largeur maximale au plus 2. Une
ressource exacte [n-1,...,0] de taille n est consommee jusqu'a l'endpoint,
qui a profondeur n et est structurellement terminal.

Une premiere comptabilite structurelle et certificate-level est fermee :

~~~text
stepCount = n
frontierSlotCount = 3n+1
structuralWorkUnits = 4n+1
provenance endpoint = n decisions
transport-code atoms = n
surface de verification relationnelle explicitement bornee
~~~

Un separateur negatif est aussi ferme : sous tout flip fixe annonce,
isolatedFrontier n est une frontiere viable de largeur n, search-irreductible,
bien que tous ses residuels soient syntaxiquement vides. La provenance suffit a
les distinguer pour ce moteur.

La couche quantitative executable est maintenant structuree de bout en bout pour
les regimes annonces : normalisation quadratique en largeur, charges binaires,
recherche dans TransportClosure, profils multidimensionnels, fermeture
input-polynomiale et passage conditionnel vers un cout machine.

Le programme annonce est clos. Les regimes supplementaires de fuel/candidats, SAT general, les ponts machine concrets et les consequences generales de classes ne sont plus des obligations de ce chantier.

Le pont classique minimal conserve la decision extensionnelle mais n'est pas fidele a toute la structure constitutive : la perte de reconstructibilite relationnelle et la perte d'information sur le cout d'organisation sont formalisees par les theoremes de non-factorisation.

Les comparaisons externes restent des audits de nouveaute et de positionnement. Elles ne definissent pas le mecanisme constitutif et ne rouvrent pas le programme scientifique.
