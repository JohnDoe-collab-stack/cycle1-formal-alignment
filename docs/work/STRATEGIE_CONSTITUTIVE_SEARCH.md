# Strategie auditee - recherche constitutive et calcul par trajectoire

## Statut du document

Ce document est le plan scientifique de travail de la branche `research/constitutive-search`.

Version auditee le 17 septembre 2026 contre le code du commit de reference :

```text
36d3ae581eaca839bde225dd2bdfde4cd24a5175
```

Le code de ce commit a passe les gates Linux et Windows du projet, y compris le build Lean, la bibliotheque de regressions et les controles de manifeste.

Ce document est un document de chantier. Il ne constitue aucune revendication sur `P = NP`. Il doit rester distinct de la documentation scientifique canonique tant que les resultats de la branche ne sont pas stabilises.

---

## 1. Idee directrice

Le programme formalise une classe de calculs ou le chemin de resolution n'est pas un objet donne a l'avance puis parcouru par une procedure externe.

Le chemin est constitue pendant le calcul.

Les determinations deja produites deviennent des donnees structurelles qui conditionnent les transformations disponibles aux etapes suivantes.

La chaine conceptuelle visee est :

```text
etat constitue
-> continuations possibles
-> relations localement reconstructibles
-> transports entre espaces de continuations
-> absorption certifiee de certaines alternatives
-> nouvelle frontiere active
-> nouvelles determinations
-> nouveau contexte relationnel
-> nouvelle etape de calcul
```

La question centrale n'est pas :

```text
quelle branche contient une solution ?
```

La question centrale est :

```text
quelles transformations positives entre futurs possibles peut-on reconstruire
sans connaitre a l'avance la positivite des branches ?
```

---

## 2. Regle methodologique principale

Le travail suit la discipline :

```text
affaiblir
-> separer
-> reconstruire
```

Aucune propriete forte ne doit etre introduite seulement parce qu'elle rend une preuve possible.

En particulier, les primitives suivantes sont interdites lorsqu'elles cachent la difficulte recherchee :

```text
la branche retenue est satisfiable
la branche eliminee est insatisfiable
une solution existe ici
aucune solution n'existe ici
le bon choix est cette branche
```

La primitive positive minimale reste de la forme :

```text
Completion source -> Completion target
```

Une propriete existentielle doit etre derivee de cette construction, jamais utilisee pour la fabriquer.

---

## 3. Ordre de dependance revise

La premiere version du plan placait SAT presque uniquement apres la couche de complexite. Le code a montre que cet ordre etait trop rigide.

SAT est utile beaucoup plus tot comme instance de validation structurelle, a condition que la complexite ne soit pas introduite prematurement.

L'ordre de travail revise est :

```text
noyau positif de transport
-> split exact
-> reduction de frontiere
-> recherche relationnelle
-> irreductibilite relative a la recherche
-> normalisation finie
-> largeur derivee
-> instance SAT structurelle minimale
-> provenance recursive des branches
-> transport entre branches avec provenance
-> etat global de recherche genere
-> trajectoire complete de frontieres
-> fermeture et composition des transports
-> ancres dynamiques
-> progression structurelle et terminalite
-> familles positives et familles separatrices
-> taille des representations et cout local
-> theorematisation de complexite
-> audit externe de nouveaute et de litterature
-> audit P/NP uniquement si toutes les gates precedentes sont fermees
```

SAT sert donc d'abord de banc d'essai formel. Les conclusions de complexite viennent seulement apres.

---

## 4. Etat reel de la formalisation au commit audite

### 4.1 Noyau generique deja formalise

Les modules suivants existent et sont integres au build.

```text
ConstitutiveSearch/ContinuationTransport.lean
ConstitutiveSearch/FrontierReduction.lean
ConstitutiveSearch/RelationalTransport.lean
ConstitutiveSearch/IrreducibleFrontier.lean
ConstitutiveSearch/ConstitutiveWidth.lean
ConstitutiveSearch/FiniteFrontierNormalization.lean
```

Ils fournissent deja :

```text
transport directionnel de completions
composition des transports
split binaire exact
frontiere proof-relevant
absorption gauche et droite
recherche executable de relations
classification directionnelle
irreductibilite relative a une recherche
reduction certifiee d'une paire
largeur derivee d'une reduction
normalisation constructive d'une frontiere finie
```

### 4.2 Instance SAT deja formalisee

Les modules SAT suivants existent et sont integres au build.

```text
ConstitutiveSearch/SAT/ConstraintTransport.lean
ConstitutiveSearch/SAT/BinaryBranch.lean
ConstitutiveSearch/SAT/RestrictionTransport.lean
ConstitutiveSearch/SAT/ResidualFlipTransport.lean
ConstitutiveSearch/SAT/ResidualTrajectory.lean
ConstitutiveSearch/SAT/BranchContext.lean
ConstitutiveSearch/SAT/BranchContextTransport.lean
```

Ils fournissent deja :

```text
syntaxe CNF minimale et satisfaction constructive
affaiblissement de CNF avec transport de completions
split exact d'une completion par valeur booleenne
residuel de branche avec witness de weakening
reconstruction du probleme parent depuis le residuel et la valeur fixee
flip de polarite sur une variable et transport des completions
trajectoire residuelle finie
contexte de branche avec historique explicite des decisions
split recursif des contextes
reconstruction d'un carrier de contexte depuis affectation, satisfaction et provenance
flip entre deux enfants d'un meme parent avec preservation des decisions anterieures
recherche executable de ce transport
largeur derivee directement sur des branches porteuses de provenance
```

### 4.3 Regressions deja presentes

La branche possede notamment des regressions pour :

```text
transport directionnel sans inverse automatique
transport non injectif
reduction de paire
irreductibilite relative a la recherche
largeur derivee
normalisation de frontiere finie
affaiblissement CNF
split SAT exact
restriction residuelle
flip entre residuels
trajectoire residuelle
provenance recursive des decisions
transport entre contextes SAT avec preservation d'une decision anterieure
largeur 1 sur une bifurcation SAT contextuelle symetrique
```

---

## 5. Ce que le noyau actuel etablit exactement

### 5.1 Transport directionnel

Un `ContinuationTransport` est une transformation positive :

```text
Completion source -> Completion target
```

Il ne suppose pas :

```text
injectivite
surjectivite
inverse
unicite
canonicalite
```

C'est intentionnel.

### 5.2 Frontiere proof-relevant

`FrontierCompletion` represente une completion portee par l'un des etats d'une liste finie.

La frontiere ne dit pas quelle branche est positive.

Elle materialise la disjonction des espaces de completions sans la reduire a une proposition booleenne.

### 5.3 Absorption

Si un transport est construit d'une branche vers une autre branche deja presente dans la frontiere, la premiere peut etre absorbee.

Cette operation ne demande pas si la branche absorbee possede effectivement une completion.

### 5.4 Irreductibilite actuelle

`SearchIrreducible search frontier` signifie seulement que la procedure `search.find` ne trouve aucun witness directionnel direct entre les paires pertinentes de la frontiere.

Cela ne signifie pas :

```text
aucun transport mathematique n'existe
aucun transport compose n'existe
aucun autre moteur de recherche ne pourrait trouver une relation
```

Cette relativite doit rester explicite dans toute documentation future.

### 5.5 Largeur actuelle

`IrreducibleFrontierReduction.width` est la longueur de la frontiere retenue apres qu'une reduction certifiee a deja ete construite.

La largeur ne choisit pas les survivants.

Elle mesure le resultat d'une construction anterieure.

### 5.6 Normalisation finie actuelle

`normalizeFrontier` est une normalisation par insertion.

Elle normalise d'abord la queue de la liste, puis insere la tete contre la frontiere deja irreductible.

Cette procedure est constructive et conserve les completions.

Elle n'est pas actuellement declaree canonique.

Elle n'est pas actuellement prouvee independante de l'ordre de la liste.

Dans un cas bidirectionnel, la reduction de paire retient un cote determine par l'implementation.

Par consequent, `normalizedWidth` doit etre traite comme une mesure operationnelle relative a :

```text
la procedure de recherche de relations
la procedure de normalisation
l'ordre de la frontiere
les generateurs de transports disponibles
```

Il ne faut pas l'appeler sans qualification "la largeur du probleme".

---

## 6. Distinction revisee des notions de largeur

Le chantier doit maintenant distinguer plusieurs niveaux.

### 6.1 Largeur d'une reduction certifiee

Deja formalisee.

```text
largeur = nombre d'etats retenus par cette reduction precise
```

Cette notion est locale a un certificat donne.

### 6.2 Largeur operationnelle normalisee

Deja calculable avec `normalizeFrontier`.

Elle depend de l'algorithme de normalisation et de l'ordre des etats.

C'est la bonne notion pour mesurer une procedure executable concrete.

### 6.3 Largeur relative a une fermeture de transports

A construire.

Une frontiere directement irreductible peut devenir reductible si des transports elementaires peuvent etre composes.

Il faudra distinguer :

```text
irreductible sous recherche directe
irreductible sous chemins de transports reconstructibles
```

### 6.4 Largeur minimale certifiable

A envisager seulement si elle devient scientifiquement utile.

Cette notion mesurerait la plus petite frontiere atteignable parmi une classe explicitement definie de reductions certifiees.

Elle ne doit pas etre introduite comme primitive de calcul.

Sa recherche pourrait elle-meme etre difficile.

Il faut donc separer clairement :

```text
mesure mathematique minimale
procedure executable qui produit une reduction
```

---

## 7. Premiere lacune generique a fermer : preservation dans les deux sens de l'existence

Les structures actuelles enregistrent principalement un transport :

```text
frontiere source -> frontiere retenue
```

Cela suffit pour montrer qu'une completion source n'est pas perdue.

Pour une procedure de decision complete, il faut aussi enregistrer ou reconstruire le fait que les etats retenus proviennent legitimement de la frontiere source.

Dans les absorptions actuelles, cette propriete est vraie structurellement parce que l'etat retenu etait deja present dans la frontiere source.

Dans `insertIntoIrreducible`, une information `retainedFromSource` est deja transportee localement pour prouver l'irreductibilite finale.

Cette provenance est toutefois perdue dans l'interface finale `IrreducibleFrontierReduction`.

### Objectif

Introduire une couche generique de preservation de frontiere qui fournisse deux transformations :

```text
FrontierCompletion source -> FrontierCompletion target
FrontierCompletion target -> FrontierCompletion source
```

Ces deux transformations n'ont pas besoin d'etre inverses.

Le but est seulement d'obtenir constructivement :

```text
Nonempty source <-> Nonempty target
```

sans importer les exigences de `ExactTypeTransport`.

### Gate

Aucune completion terminale ne doit pouvoir etre interpretee comme un temoin de l'instance initiale sans chemin constructif de retour vers la frontiere initiale.

---

## 8. Deuxieme lacune : fermeture et composition des relations

La recherche actuelle est paire par paire et directe.

Si la procedure trouve :

```text
A -> B
B -> C
```

alors le noyau sait composer les transports et construire :

```text
A -> C
```

Mais l'irreductibilite actuelle ne demande pas si un tel chemin compose existe.

### Objectif semantique

Definir un witness proof-relevant de chemin de transports elementaires.

Par exemple conceptuellement :

```text
TransportPath A B
```

avec :

```text
identite
pas elementaire
composition
```

### Objectif executable

La recherche de chemins doit rester distincte de l'existence abstraite d'un chemin.

On devra donc separer :

```text
fermeture mathematique des generateurs
procedure executable de recherche dans cette fermeture
cout de cette recherche
```

### Gate

Ne jamais declarer une frontiere globalement irreductible parce que les recherches directes echouent si la classe annoncee de reductions autorise la composition.

---

## 9. Troisieme lacune : etat global de branche SAT

`ContextFlipRelation parent var source target` compare actuellement deux enfants booleens d'un meme parent et d'une meme variable.

C'est suffisant pour la regression actuelle.

Ce n'est pas encore une relation sur une frontiere recursive heterogene de `BranchContext` provenant de parents differents.

### Objectif

Introduire un etat SAT genere qui porte explicitement :

```text
le BranchContext courant
un witness de reconstruction du carrier
la provenance de generation depuis la racine
les invariants de fraicheur utiles
```

Nom de travail possible :

```text
GeneratedBranchContext
```

La definition exacte doit etre derivee des besoins des preuves, pas du nom.

### Completion globale

La famille de completions doit devenir indexee directement par l'etat genere :

```text
GeneratedBranchCompletion state
```

### Relation globale

Il faudra ensuite definir des relations entre deux etats generes, potentiellement issus de parents differents.

Chaque witness devra prouver explicitement comment l'affectation, la satisfaction et la provenance cible sont reconstruites.

### Gate

Aucun oubli de provenance ne doit etre justifie uniquement par une egalite de formules residuelles.

---

## 10. Reconstruction des carriers et statut de `BranchContext`

`BranchContext` reste volontairement abstrait sur son `Carrier`.

Tous les `BranchContext` arbitraires ne sont donc pas automatiquement reconstruisibles depuis :

```text
affectation
satisfaction
historique de decisions
```

Le module `BranchContextTransport` introduit separement :

```text
BranchContextReconstruction context
```

Cette interface est disponible pour la racine et se propage aux enfants generes.

### Decision d'architecture

Ne pas renforcer `BranchContext` en lui ajoutant automatiquement cette propriete.

Conserver la separation :

```text
contexte abstrait
contexte reconstructible
contexte effectivement genere par la recherche SAT
```

Cela permet de construire des separateurs et d'eviter d'introduire une reconstruction non justifiee comme primitive universelle.

---

## 11. Semantique exacte du residuel SAT actuel

Le residuel actuellement implemente est volontairement faible.

Pour une valeur de branche, `branchResidual` :

```text
supprime une clause si elle contient le litteral rendu vrai par la decision
conserve les autres clauses sans supprimer le litteral rendu faux
```

Ce n'est donc pas encore la restriction CNF standard completement simplifiee.

Cette construction est neanmoins correcte pour le modele actuel parce que les completions residuelles conservent explicitement la valeur fixee de la variable.

### Consequence

Toute documentation doit parler de :

```text
residuel par suppression de clauses satisfaites
```

et non d'une simplification SAT standard complete.

### Extension future

Ajouter, separement, une restriction plus forte qui :

```text
supprime les clauses satisfaites
supprime le litteral falsifie dans les clauses restantes
```

Puis reconstruire les transports entre :

```text
branche exacte
residuel faible actuel
residuel simplifie
```

### Gate

Ne jamais remplacer silencieusement le residuel faible par une notion syntaxique plus forte sans theorem de correspondance des completions.

---

## 12. Trajectoire complete de frontieres

Le module `ResidualTrajectory` actuel est une trajectoire lineaire de CNF residuelles.

`SATBranchContextRegression` construit egalement plusieurs niveaux de branchement.

Il manque encore un objet generique qui fasse de la trajectoire complete un objet proof-relevant de premier rang.

### Objet cible

Un pas de trajectoire doit contenir au minimum :

```text
frontiere source
expansion exacte
frontiere developpee
reduction certifiee
frontiere retenue
provenance des etats retenus
```

Conceptuellement :

```text
F_k
-> expansion exacte
G_k
-> reduction certifiee
F_(k+1)
```

### Histoire de frontieres

Une trajectoire doit composer ces pas :

```text
F_0 -> F_1 -> ... -> F_n
```

et transporter les completions de bout en bout.

### Theoreme prioritaire

Construire un theorem de conservation de l'existence dans les deux sens pour toute trajectoire composee, en utilisant la couche de provenance de la section 7.

Ce theorem doit etre obtenu avant toute analyse de complexite globale.

---

## 13. Ancres dynamiques

L'idee "le chemin est le calcul" ne sera pleinement formalisee que lorsqu'une determination nouvelle changera effectivement les relations reconstructibles ensuite.

Les decisions de `BranchContext` donnent deja une premiere forme de provenance dynamique.

Le transport contextuel actuel montre qu'une relation future doit respecter les decisions anterieures.

Il ne montre pas encore un cas ou une nouvelle determination rend disponible un transport qui etait auparavant introuvable.

### Milestone central

Construire une instance ou :

```text
au niveau k
la recherche relationnelle ne trouve pas de transport entre deux continuations

apres une nouvelle determination d_k
la provenance ou une nouvelle ancre rend un witness relationnel reconstructible

ce nouveau transport reduit la frontiere au niveau k + 1
```

C'est le test formel direct de l'hypothese centrale du programme.

### Gate

Une "ancre" doit changer une capacite de reconstruction, pas seulement ajouter un label a l'etat.

---

## 14. Progression structurelle SAT

La terminaison ne doit pas etre definie uniquement par un compteur externe.

Pour l'instance SAT recursive, la structure de provenance suggere un candidat concret :

```text
chaque split legal ajoute une nouvelle decision sur une variable fraiche
```

### Travail a faire

Definir les variables pertinentes de l'instance initiale comme un objet fini.

Etablir :

```text
chaque decision de l'histoire porte sur une variable pertinente
aucune variable n'est decidee deux fois le long d'une histoire legale
une etape non terminale ajoute une nouvelle variable decidee
```

La borne numerique sur la profondeur doit ensuite etre derivee du nombre fini de variables pertinentes.

### Gate

La longueur de l'histoire ne doit pas servir a justifier retroactivement la fraicheur. La fraicheur est une propriete structurelle de la transition.

---

## 15. Generateurs de transports SAT

Chaque generateur doit etre traite comme une couche scientifique separee.

Pour chaque generateur, exiger quatre objets :

```text
type de witness structurel
action constructive sur les completions
procedure executable de recherche du witness
preuve de correction de cette recherche lorsqu'elle retourne un witness
```

La complexite de la recherche sera ajoutee plus tard.

### 15.1 Deja present : affaiblissement de CNF

Un witness de weakening transporte une completion d'une formule plus contrainte vers une formule moins contrainte.

### 15.2 Deja present : flip de polarite

Un flip couple sur la formule et l'affectation transporte les completions lorsque les residuels sont exactement relies par cette transformation.

### 15.3 Deja present : lift du flip au contexte

Le flip peut etre eleve aux vrais enfants `BranchContext` lorsqu'il preserve l'historique deja constitue et que le carrier parent est reconstructible.

### 15.4 Prochain : renommage de variables

Formaliser des permutations ou renommages finis avec action explicite sur :

```text
litteraux
clauses
CNF
affectations
histoires de decisions
```

### 15.5 Prochain : restriction SAT simplifiee

Introduire la suppression du litteral falsifie et prouver sa relation au residuel faible actuel.

### 15.6 Prochain : substitutions directionnelles

Tester des transformations qui transportent les completions sans etre necessairement inversibles.

### 15.7 Prochain : propagation certifiee

Traiter propagation unitaire, simplification locale et autres operations seulement lorsque leur action sur les completions est explicite.

### 15.8 Composition

Les generateurs elementaires doivent pouvoir produire des chemins de transports plus riches sans appel a un solveur global.

---

## 16. Familles positives a viser

Avant SAT general, il faut obtenir des theoremes parametriques sur des familles non triviales.

### 16.1 Premiere cible : famille symetrique parametrique

Construire une famille avec plusieurs blocs de la forme generale :

```text
(x_i OR y_i)
AND
(NOT x_i OR y_i)
```

ou une variante adaptee au residuel formel courant.

L'objectif est de prouver par induction que les deux enfants produits sur chaque `x_i` sont relies par un transport structurel explicite et que la frontiere reste de largeur operationnelle 1 sous la strategie definie.

Cette cible generalise directement les regressions symetriques actuelles.

### 16.2 Deuxieme cible : familles ou weakening et symetries composent

Chercher une famille ou aucun generateur pris seul ne suffit, mais ou leur composition controle la frontiere.

Cette cible testera reellement la fermeture des transports.

### 16.3 Cibles ulterieures

Apres stabilisation du moteur :

```text
2-SAT
Horn-SAT
CSP de largeur bornee
familles de CNF avec parametres structurels controles
```

Le but n'est pas de redemontrer artificiellement leur tractabilite.

Le but est de voir si la largeur constitutive explique une structure algorithmique identifiable.

---

## 17. Familles separatrices obligatoires

Les separateurs sont aussi importants que les cas positifs.

### 17.1 Aucun transport trouve

Construire une famille ou la frontiere double sous les splits parce que le moteur relationnel choisi ne trouve aucune absorption.

### 17.2 Weakening seul insuffisant

Construire une famille ou les branches ne sont pas comparables par weakening alors qu'une autre transformation serait disponible.

### 17.3 Flip seul insuffisant

Construire une famille asymetrique ou le flip exact ne s'applique pas et ou la largeur augmente.

### 17.4 Irreductibilite directe mais reductibilite composee

Construire trois etats :

```text
A
B
C
```

avec transports elementaires permettant un chemin utile sans relation directe trouvee entre certaines extremites.

Ce separateur doit justifier la couche de fermeture par composition.

### 17.5 Sensibilite a l'ordre de normalisation

Construire une instance ou deux ordres de la meme frontiere donnent des representants differents, et si possible des largeurs operationnelles differentes.

Si aucune difference de largeur n'est possible sous les invariants actuels, le prouver.

Ne pas supposer l'independance a l'ordre.

### 17.6 Petite frontiere, gros certificats

Construire une interface ou la frontiere est petite mais les witnesses relationnels grossissent rapidement.

### 17.7 Provenance incompatible

Construire deux etats syntaxiquement proches ou egaux dont les historiques de decisions empechent un transport contextuel annonce.

### 17.8 Progression locale sans borne globale

Construire un systeme abstrait avec transitions strictes mais sans borne raisonnable de profondeur.

---

## 18. Correction d'une procedure de decision

Une procedure complete doit distinguer deux questions.

### 18.1 Preservation pendant le calcul

Les expansions et reductions doivent conserver l'existence d'une completion pertinente.

### 18.2 Interpretation terminale

Les etats terminaux doivent disposer d'une decision directe ou d'un certificat direct de leur statut relativement a l'instance initiale.

Pour SAT, le chemin naturel est :

```text
frontiere initiale
-> splits exacts et reductions certifiees
-> frontiere terminale finie
-> completions terminales correspondant a des affectations completes
-> verification directe de la formule
```

La verification terminale ne doit jamais guider retroactivement les choix de reduction.

---

## 19. Couche de complexite, seulement apres la correction structurelle

Aucun mot "polynomial" ne doit porter la preuve d'une etape structurelle.

Une fois la trajectoire correcte, introduire explicitement les quantites suivantes.

### 19.1 Taille d'entree

Definir une taille encodee de l'instance initiale.

### 19.2 Profondeur

Nombre maximal d'etapes constitutives avant terminalite.

### 19.3 Largeur operationnelle

Nombre maximal d'etats actifs produits par l'algorithme de normalisation choisi.

### 19.4 Taille d'etat

Taille de :

```text
formule residuelle
historique de decisions
contexte d'ancres
donnees de reconstruction
```

### 19.5 Taille des witnesses

Taille des preuves ou certificats structurels necessaires pour appliquer un transport.

### 19.6 Cout de recherche

Cout de :

```text
expansion
recherche de relation
recherche dans la fermeture de relations
construction du transport
normalisation de frontiere
verification terminale
```

### 19.7 Theoreme conditionnel vise

Seulement apres definition de ces quantites :

> si profondeur, largeur operationnelle, tailles de representations, tailles de witnesses et couts locaux sont tous bornes polynomialement dans la taille d'entree, alors la procedure executable correspondante a un cout polynomial.

Ce theorem est une consequence de l'interface de cout. Il ne doit pas etre utilise pour fabriquer les bornes.

---

## 20. Audit de nouveaute et positionnement par rapport a la litterature

Le programme possede des voisins conceptuels importants.

Avant toute revendication de nouveaute, comparer formellement ou textuellement la construction avec au moins :

```text
P-selectivity et auto-reduction
simulation et preordres de dominance
algorithmes par antichaines
BDD, OBDD et branching programs
subsumption et reduction symbolique d'espaces d'etats
CSP de largeur bornee et coherence locale
parametres de largeur tels que treewidth et pathwidth
DPLL, CDCL et complexite des preuves
```

Le but de cet audit est de repondre a des questions precises :

```text
la largeur constitutive est-elle deja une largeur connue sous une autre presentation ?
le transport de completions est-il un preorder de simulation standard dans une instance donnee ?
la provenance des branches ajoute-t-elle une structure absente de ces modeles ?
les ancres dynamiques donnent-elles un pouvoir de reconstruction reellement different ?
les bornes positives ou negatives se traduisent-elles dans un parametre connu ?
```

Aucune revendication de nouveaute conceptuelle ne doit preceder cet audit.

---

## 21. Gates anti-triche revisees

### Gate A - aucune decision SAT cachee

Aucune construction de transport ne peut utiliser comme entree une decision generale de satisfaisabilite ou d'insatisfaisabilite de la branche.

### Gate B - witness positif

Toute absorption doit etre justifiee par une transformation effective des completions ou par une construction dont cette transformation est derivee.

### Gate C - `none` reste un echec de recherche

Un echec de `search.find` n'est pas une preuve d'inexistence sans theorem de completude explicite.

### Gate D - provenance des survivants

Une frontiere retenue doit rester reliee constructivement a la frontiere source dans le sens necessaire a l'interpretation terminale.

### Gate E - pas de quotient gratuit

Deux etats ayant la meme lecture ou la meme formule residuelle ne sont pas identifies sans theorem permettant d'oublier leur provenance.

### Gate F - fermeture annoncee honnetement

Si la classe de transports autorise la composition, l'irreductibilite doit etre qualifiee relativement a la recherche directe ou a la fermeture effectivement exploree.

### Gate G - largeur qualifiee

Toujours preciser s'il s'agit de :

```text
largeur d'un certificat
largeur operationnelle de l'algorithme courant
largeur relative a une fermeture
largeur minimale abstraite
```

### Gate H - taille des representations

Une petite largeur ne suffit pas si les etats ou witnesses ont une taille superpolynomiale.

### Gate I - profondeur

Une transition stricte ne suffit pas si le nombre d'etapes n'est pas controle.

### Gate J - execution constructive

Aucun `sorry`, aucun axiome ajoute, aucun `noncomputable` et aucune classicalisation silencieuse dans les couches executables de la branche.

### Gate K - generalite SAT

Toute conclusion sur SAT general exige que les generateurs et bornes couvrent toutes les instances de la classe annoncee.

### Gate L - decision terminale separee de la construction

Le test final d'un temoin ne peut pas etre utilise pour fabriquer le chemin qui conduit a ce temoin.

---

## 22. Architecture Lean revisee

### 22.1 Modules generiques existants

```text
ConstitutiveSearch/
  ContinuationTransport.lean             [fait]
  FrontierReduction.lean                 [fait]
  RelationalTransport.lean               [fait]
  IrreducibleFrontier.lean               [fait]
  ConstitutiveWidth.lean                 [fait]
  FiniteFrontierNormalization.lean       [fait]
```

### 22.2 Prochains modules generiques probables

Les noms restent provisoires.

```text
ConstitutiveSearch/
  FrontierPreservation.lean              [prochain]
  TransportClosure.lean                  [prochain]
  FrontierTrajectory.lean                [prochain]
  DynamicAnchors.lean                    [apres trajectoire]
  StructuralProgress.lean                [apres etat global]
  ComplexityInterface.lean               [tardif]
```

### 22.3 Modules SAT existants

```text
ConstitutiveSearch/SAT/
  ConstraintTransport.lean               [fait]
  BinaryBranch.lean                      [fait]
  RestrictionTransport.lean              [fait]
  ResidualFlipTransport.lean             [fait]
  ResidualTrajectory.lean                [fait, lineaire seulement]
  BranchContext.lean                     [fait]
  BranchContextTransport.lean            [fait, enfants d'un meme parent]
```

### 22.4 Prochains modules SAT probables

```text
ConstitutiveSearch/SAT/
  GeneratedContext.lean                  [prochain]
  GlobalContextRelation.lean             [prochain]
  ContextFrontier.lean                   [prochain]
  ContextTrajectory.lean                 [prochain]
  RenamingTransport.lean                 [ensuite]
  SimplifiedRestriction.lean             [ensuite]
  SubstitutionTransport.lean             [ensuite]
  PropagationTransport.lean              [ensuite]
  ParametricSymmetricFamily.lean         [benchmark positif]
  WidthSeparators.lean                   [benchmark negatif]
```

---

## 23. Phases revisees et statut reel

### Phase A - noyau directionnel

Statut : fait.

Gate : verte.

### Phase B - frontiere proof-relevant et reductions

Statut : fait pour les operations de base.

Gate restante : ajouter la preservation inverse de provenance au niveau generique.

### Phase C - recherche relationnelle et irreductibilite

Statut : fait pour la recherche directe.

Gate restante : distinguer et formaliser la fermeture composee.

### Phase D - largeur et normalisation finie

Statut : fait au niveau operationnel.

Gate restante : tester la sensibilite a l'ordre et clarifier la hierarchie des largeurs.

### Phase E - SAT structurel minimal

Statut : fait.

Le split, le residuel, le weakening et le flip sont disponibles.

### Phase F - provenance recursive SAT

Statut : fait pour des branches generees recursivement.

Le transport contextuel preserve deja une decision anterieure dans la regression actuelle.

### Phase G - etat SAT global heterogene

Statut : prochain verrou principal.

Livrables :

```text
etat genere
reconstruction attachee
relation entre etats de parents differents
frontiere de tels etats
```

### Phase H - trajectoire complete

Statut : a construire.

Livrables :

```text
suite de frontieres
expansion puis reduction par etape
provenance composee
conservation de l'existence dans les deux sens
```

### Phase I - fermeture de transports

Statut : a construire.

Livrables :

```text
chemins proof-relevant de transports
recherche executable de chemins
separateur direct vs compose
```

### Phase J - ancres dynamiques

Statut : a construire apres stabilisation de l'etat global.

Gate centrale : une nouvelle determination doit rendre reconstructible un transport auparavant indisponible.

### Phase K - progression et terminalite

Statut : a construire.

Premiere cible SAT : decisions sur variables pertinentes sans repetition.

### Phase L - familles positives et negatives

Statut : a construire.

Commencer par la famille symetrique parametrique et des separateurs synthetiques.

### Phase M - complexite

Statut : interdit tant que les phases G a L ne sont pas stabilisees.

### Phase N - audit de nouveaute

Statut : a mener en parallele des premiers theoremes parametriques, avant toute communication de nouveaute forte.

### Phase O - audit P/NP

Statut : non ouvert.

Il ne devient legitime que si une instance SAT generale et ses bornes globales sont effectivement prouvees.

---

## 24. Sequence d'implementation immediate

L'ordre recommande apres l'audit est maintenant :

```text
1. FrontierPreservation
2. regression montrant Nonempty source <-> Nonempty retenue pour une absorption
3. preservation correspondante pour normalizeFrontier
4. GeneratedBranchContext
5. relation globale entre contextes generes
6. frontiere heterogene de contextes SAT
7. FrontierTrajectory generique
8. trajectoire SAT de plusieurs niveaux avec reduction a chaque niveau
9. TransportClosure et separateur direct vs compose
10. test de sensibilite a l'ordre du normaliseur
11. famille SAT symetrique parametrique avec borne de largeur
12. premier exemple d'ancre dynamique qui debloque un transport
13. progression par variables fraiches et borne de profondeur
14. seulement ensuite premiers comptes de taille et de cout
```

Cet ordre remplace l'ancienne sequence qui commencait directement par `DynamicAnchors`.

La raison est maintenant prouvee par l'experience de formalisation : les ancres dynamiques ne peuvent etre evaluees proprement avant d'avoir un etat global, une trajectoire et une notion precise de preservation de frontiere.

---

## 25. Premier theorem global vise

Le prochain grand resultat ne doit pas parler de complexite.

Forme cible :

> Pour toute trajectoire finie construite par splits exacts et absorptions certifiees, une completion de la frontiere initiale peut etre transportee vers la frontiere finale, et toute completion de la frontiere finale peut etre interpretee constructivement comme une completion de la frontiere initiale.

Ce resultat donne :

```text
Nonempty frontiere initiale
<->
Nonempty frontiere finale
```

sans exiger que les transports d'absorption soient inversibles.

C'est le socle correct pour une procedure de decision.

---

## 26. Premier theorem SAT parametrique vise

Apres le theorem global de trajectoire :

> Une famille parametrique de CNF a symetries locales explicites admet une trajectoire de contextes dans laquelle chaque split sur une variable fraiche est suivi d'une absorption contextuelle certifiee, et la largeur operationnelle de la frontiere reste egale a 1 le long de la strategie definie.

Ce theorem doit etre prouve pour une famille de taille arbitraire, pas seulement pour un exemple ferme.

Il fournira le premier test de passage :

```text
regression locale
-> theorem de famille
```

---

## 27. Premier theorem separateur vise

Construire une famille ou une interface de transports explicitement limitee ne controle pas la largeur.

Forme cible :

> Sous le moteur relationnel R choisi, la frontiere produite par la strategie S contient au moins k etats irreductibles apres k etapes, ou suit une autre croissance explicite.

Le but n'est pas necessairement d'obtenir immediatement une borne exponentielle.

Le premier objectif est de formaliser proprement une impossibilite relative a une interface annoncee.

---

## 28. Criteres de valeur scientifique independants de P/NP

Le chantier possede un interet propre si au moins un des resultats suivants est obtenu.

### Resultat A

Une theorie generique constructive de reduction de recherche par transports directionnels avec provenance de frontiere.

### Resultat B

Une hierarchie propre entre largeur directe, largeur operationnelle, largeur fermee par composition et largeur minimale certifiable.

### Resultat C

Des theoremes parametriques expliquant la tractabilite de familles de contraintes par des transports de futurs.

### Resultat D

Des separateurs montrant exactement quelles interfaces relationnelles echouent a controler la frontiere.

### Resultat E

Un mecanisme d'ancres dynamiques ou le chemin constitue de nouvelles capacites de reduction.

### Resultat F

Une correspondance ou une separation rigoureuse entre cette theorie et une notion existante de simulation, antichaines, branching programs ou largeur de CSP.

---

## 29. Conditions avant toute revendication de complexite forte

Aucune conclusion telle que `SAT est en P` ou `P = NP` ne peut etre formulee comme resultat du projet tant que toutes les conditions suivantes ne sont pas fermees.

1. L'instance couvre exactement la classe SAT annoncee.
2. Les splits sont exacts au niveau des completions.
3. Les reductions conservent les completions sources.
4. Les completions retenues restent interpretables dans la source.
5. Les transports sont reconstruits depuis des witnesses structurels explicites.
6. Les procedures de recherche n'utilisent aucune decision SAT cachee.
7. La fermeture des transports utilisee par l'algorithme est explicitement definie.
8. La profondeur globale est bornee polynomialement.
9. La largeur operationnelle globale est bornee polynomialement.
10. La taille des etats est bornee polynomialement.
11. La taille des historiques et ancres est bornee polynomialement.
12. La taille des witnesses de transport est bornee polynomialement.
13. Le cout de recherche des relations et de leurs compositions est borne polynomialement.
14. Le cout de normalisation de la frontiere est borne polynomialement.
15. La procedure terminale est executable et correcte.
16. Les preuves Lean n'utilisent aucun axiome interdit.
17. Les separateurs connus ne refutent pas l'interface finale annoncee.
18. Le modele de cout a ete audite independamment de la preuve structurelle.
19. Le positionnement par rapport aux resultats connus a ete verifie.
20. Un audit externe du resultat complet a ete effectue avant toute communication forte.

Si une seule de ces conditions manque, le statut reste conditionnel ou exploratoire.

---

## 30. Discipline de branche

Sur `research/constitutive-search` :

```text
commits petits et auditables
regression avec chaque nouvelle couche
AXIOM_AUDIT dans chaque fichier Lean scientifique
aucun sorry
aucun noncomputable
aucun Classical introduit silencieusement
aucun merge vers main sans demande explicite
```

Pour les changements structurels importants :

```text
travailler si utile sur une branche de validation
laisser le CI Linux et Windows passer
fast-forward seulement apres validation
```

Avant toute pull request vers `main` :

```text
convertir ou supprimer ce document de chantier
mettre a jour la documentation scientifique canonique
mettre a jour le manifeste si necessaire
verifier lake build
verifier AuditRegression
verifier les audits axiomatiques
scanner noncomputable et sorry
nettoyer les branches ou fichiers temporaires utiles seulement au chantier
```

---

## 31. Resume audite du programme

La chaine scientifique revisee est :

```text
etats constitues
-> espaces de completions
-> splits exacts
-> relations structurelles
-> transports directionnels
-> absorption certifiee
-> provenance des survivants
-> frontiere irreductible relative a une recherche
-> normalisation finie operationnelle
-> contexte SAT recursif avec provenance
-> etat global genere
-> trajectoire complete de frontieres
-> composition et fermeture des transports
-> ancres dynamiques
-> progression structurelle
-> largeur qualifiee
-> familles positives et separatrices
-> tailles et couts
-> theorem de complexite conditionnel
-> audit de nouveaute
-> seulement ensuite audit P/NP
```

Le probleme central reste :

> construire suffisamment de transformations entre futurs possibles pour reduire les alternatives sans connaitre leur positivite a l'avance.

Le prochain verrou n'est plus la construction d'un transport local sur un exemple SAT.

Ce verrou est deja franchi.

Le prochain verrou est de passer de ces transports locaux a une **trajectoire globale de frontieres porteuses de provenance**, avec preservation bidirectionnelle de l'existence, relations composables et largeur clairement qualifiee.

C'est cette etape qui transformera le noyau actuel en veritable theorie de calcul par trajectoire.
