# Plan d’implémentation — audit constitutif avec ConLeche

## Statut

Ce document est un document de chantier temporaire.

Il organise trois lignes de résultats distinctes :

1. un audit externe reproductible du dépôt avec ConLeche en mode `--verified` ;
2. une étude constitutive de la provenance et de la chaîne interne menant de
   l’acceptation à `no False` ;
3. l’étude, encore ouverte, d’un remplacement relatif de l’hypothèse globale de
   chaîne d’univers par une réalisation finie indexée par les demandes
   effectivement constituées.

Il doit être supprimé dans la pull request ou merge request qui intégrera le
chantier dans `main`. Il ne fait pas partie des livrables scientifiques finaux.

Le premier état formalisé du chantier est gelé au commit `d296630`. L’analyse β
et sa comparaison postérieure avec δ sont documentées au commit `e567f09`.
L’analyse indépendante de la branche ι `.plain` est documentée au commit
`4c285c6`. Le travail courant se poursuit sur
`codex/con-leche-beta-audit`. Avant la merge request finale, vérifier
explicitement que la branche contient ces trois jalons et tous les résultats
scientifiques attendus.

### État scientifique au présent commit

- le noyau générique de candidature, ombre propositionnelle, stabilité
  historique, reconstruction locale et séparateurs est stabilisé dans le dépôt ;
- la slice terminale de `no False` est distinguée de l’invariant inductif
  transporté par le fold ;
- δ constitue le cas de référence gelé ;
- β a été analysé indépendamment puis comparé à δ : les deux chemins convergent
  vers la même préservation gardée des appartenances ;
- le résidu ultérieur du certificat `ReducePinRun` a forcé un nouveau test ι,
  distinct du séparateur `.plain` antérieur : une occurrence réelle de
  `PUnit.rec` produisant l’identité sur `Nat` ferme localement le run, la
  lecture exacte de sa source annotée et le transport sémantique du certificat,
  sans `DefEqClaim` global ni nouvelle mémoire historique ;
- ι a été lancé indépendamment : le cas `.plain` possède un séparateur
  local porté par une exécution inductive complète, du
  `ProvisionRecsRun` interne jusqu’à `IndRecsRun`, `DeclIndRun` et `DeclRun`,
  puis jusqu’au calcul réel `checkDecl = .ok`, avec un carburant unique et la
  règle installée exacte ; son front-door RHS a été strictement affaibli à
  « lecture exacte + `WellDenotedV` uniforme » ; son environnement synthétique
  exact est maintenant prouvé improductible par `checkDeclsPure` depuis
  `Env.empty`. Un remplacement atteignable a été construit : le vrai checker
  accepte le préfixe, le vrai `PUnit.rec` exécute ι, mais l’échec sémantique y
  est déjà présent dans le minorant fourni au recursor. Ce remplacement ne
  constitue donc pas un séparateur propre à la loi ι. Conformément à la
  méthode, la recherche d’un autre séparateur ι est arrêtée tant qu’aucun nouveau
  résidu productible ne l’impose. Le chantier est revenu au résidu `defn`
  initial : un préfixe complet contenant l’application fautive est maintenant
  accepté depuis `Env.empty`, le vrai `DeclDefnRun` est construit, et la
  `GuardedMembershipPreservation` commune à δ/β est à la fois suffisante pour
  reconstruire l’obligation sémantique locale et réfutée sur le même témoin
  affaibli. L’état et la transition sont donc atteignables ; la réalisation
  affaiblie choisie sur cet état n’est pas présentée comme le témoin sémantique
  produit par le fold riche. Le premier test de réemploi d’une définition
  ancienne sous un argument ajouté ultérieurement est également fermé : deux
  déclarations `defn` successives sont acceptées depuis `Env.empty`, leurs deux
  états admettent des témoins `B0W`, et l’annotation historique exacte du type
  de l’argument peut échouer à fournir le `CtxOk` requis. Le weakening construit
  toutefois un autre représentant ouvert du même argument sémantique dans un
  contexte `Sort 1` valide. Cet échec local ne force donc aucune persistance ;
  le raccord sémantique complet du cas concret est ensuite reconstruit : le
  provider ancien, les lectures applicatives exactes et la closedness déjà
  portée par `EnvModel` suffisent à transporter l’application fermée au nouvel
  argument `.prf`. La première transition possède désormais aussi un vrai
  successeur historiquement compatible : en choisissant pour l’alias la lecture
  exacte de son corps, on construit simultanément le `WalkWitness` successeur et
  son `AdmissibleDeltaMembershipProvider`. Le successeur terminal incohérent
  antérieur sépare donc la substitution arbitraire des réalisations, pas
  l’existence d’un transport fidèle. Enfin, le run réel d’inférence d’une valeur
  produit localement le représentant ouvert requis pour un nouvel argument :
  `InferReads + InferClaim` donnent le type inféré lu, sa `WellDenotedV` et
  l’appartenance de la lecture de la valeur à ce même type. `DefEqClaim`, le type
  déclaré et `ConstantValRun` ne sont pas consommés à cet étage. La
  seconde transition concrète est elle aussi fermée positivement : la lecture
  exacte de la lambda fraîche étend la slice, appartient exactement à la
  lecture fonctionnelle de l’alias, et les deux corps stockés reconstruisent le
  provider complet dans l’environnement final. La chaîne de deux définitions
  acceptées possède ainsi un témoin historique final exact avec provider, sans
  enrichissement du carrier ;
- aucune réduction de l’hypothèse globale de chaîne d’univers n’est encore
  démontrée.

## 1. Principe scientifique

### Position du cas d’étude

Le cadre théorique est autonome et antérieur à cette étude. Il est formalisé
dans `SegmentedResidualRole`, `AbstractSegmentedTurning`,
`StrongPerimetralTurning` et le noyau générique de `VerificationTransport`.
ConLeche n’en est ni la source, ni la fondation, ni une dépendance scientifique :
il constitue un **cas d’étude externe** sur lequel ce cadre est instancié et
éprouvé.

```text
cadre théorique autonome
  → instanciation sur ConLeche
  → dissection de ses transformations et invariants réels
  → factorisations, capacités et séparateurs propres au cas étudié
```

ConLeche peut contraindre une instanciation, révéler qu’un adaptateur manque ou
réfuter une conjecture par un séparateur. Il ne doit pas définir rétroactivement
les notions générales du cadre. Une abstraction nouvelle n’entre dans le noyau
que si plusieurs preuves l’imposent indépendamment et si sa formulation ne
mentionne aucun détail propre à ConLeche.

### Protocole impératif du cas d’étude

ConLeche est analysé exclusivement par la méthode du cadre, dans cet ordre :

```text
résidu concret
→ factorisation positive
→ weakening des données consommées
→ séparateur constructif au premier échec
→ contrôle de l’atteignabilité
→ reconstruction locale ou nécessité de persistance
→ enrichissement minimal du candidat
→ nouveau test de fermeture
```

Il est interdit de remplacer un maillon manquant par une abstraction nommée,
de poursuivre une autre branche avant d’avoir classé le résidu courant, ou de
déduire une impossibilité d’un simple échec de recherche. Une capacité n’entre
dans le carrier que si sa nécessité transitionnelle, sa non-reconstructibilité
locale et sa portée d’atteignabilité ont été séparément établies. Toute
déviation invaliderait la valeur du cas d’étude comme test du cadre théorique.

Le chantier part de la distinction suivante :

```text
garantie établie sur l’acceptation terminale
≠
fidélité du transport jusqu’au checker
```

ConLeche établit une garantie forte sur la liste de déclarations acceptée par
son fold vérifié. Sa documentation distingue toutefois cette liste du flux
d’export initial, qui passe auparavant par un frontend et plusieurs
transformations.

Le contrat externe consommé par ce chantier est exactement : pour tout modèle
de l’interface `SetTheory`, si `checkDecls` en mode `verified` accepte une liste
de déclarations et produit un environnement, cet environnement ne contient pas
de constante dont le type est `False`. C’est une garantie sémantique relative,
dans la direction de l’acceptation ; ce n’est ni une preuve absolue de cohérence
ni un théorème syntaxique général `accepted → derivable`.

L’analyse constitutive ne cherche donc ni une erreur de ConLeche ni une nouvelle
preuve de sa cohérence. Elle cherche à rendre explicitement témoinisée la chaîne :

```text
source Lean
  → export
  → parsing
  → transformations frontend
  → déclarations vérifiées
  → verdict
```

La revendication centrale visée est :

```text
Accepted presented
ne construit pas, à lui seul,
FaithfullyFormedFrom source presented.
```

## 2. Trois lignes de travail à statuts indépendants

### Ligne A — audit externe

```text
commit propre et identifié
  → export régénéré
  → hash de l’export
  → ConLeche --verified sur ces mêmes octets
  → verdict et métadonnées enregistrés
```

Cette ligne produit un résultat expérimental reproductible. Elle ne produit pas
automatiquement un terme de preuve Lean dans le dépôt.

### Ligne B — analyse constitutive

```text
occurrence source
  → occurrence exportée
  → occurrence parsée
  → occurrence transformée
  → occurrence présentée au checker
```

Chaque flèche doit porter un témoin de fidélité propre. L’acceptation terminale
et la fidélité amont restent deux certificats séparés. À l’intérieur du checker,
la même discipline distingue en outre :

```text
constitution par un producteur
  → capacité exportée
  → jugement effectivement consommé
```

La slice terminale suffisante pour `no False` ne doit jamais être confondue avec
sa fermeture inductive sous `DeclRun`.

### Ligne C — réduction relative de l’hypothèse d’univers

```text
demandes d’univers concrètement évaluées
  → histoire finie de leurs occurrences sémantiques
  → clôture finie des niveaux de support requis
  → réalisation par une tour finie
  → transport des obligations nécessaires à no False
```

Cette ligne n’a pas pour point de départ un entier `k` choisi ou calculé par une
analyse syntaxique globale. Le niveau numérique est une lecture tardive de
l’histoire de support obtenue. L’histoire des usages et l’histoire des niveaux
de support restent distinctes : plusieurs usages peuvent partager un niveau,
tandis qu’un seul usage à un niveau élevé peut exiger plusieurs étapes de
support.

La Ligne A peut être fermée même si les Lignes B ou C demeurent ouvertes. La
Ligne B peut produire des factorisations et séparateurs sans fermer la Ligne C.
Aucun succès d’une ligne ne doit être présenté comme un succès d’une autre.

### Carte de couverture

| Frontière | Première garantie visée | Statut attendu |
| --- | --- | --- |
| source → export | régénération depuis un commit propre et liaison par empreinte | observation reproductible |
| export → représentation parsée | aucune fidélité globale présupposée | ouvert sauf résultat spécifique |
| parsé → présenté | témoin sur une transformation frontend précisément bornée | théorème local ou ouvert |
| présenté → acceptation | exécution de ConLeche en mode vérifié | observation couverte par le théorème relatif de ConLeche |

Cette table doit être mise à jour à mesure que les gates ferment. Une case
ouverte ne peut pas être absorbée par une garantie située en aval.

## 3. Réemploi obligatoire du noyau existant

Le chantier ne doit pas créer un second formalisme général de constitution.

Il doit d’abord réutiliser :

- `SegmentedResidualRole.ExactInternalRealization` pour les correspondances
  exactes rôle ↔ occurrence et leurs deux aller-retour ;
- `SegmentedResidualRole.FaithfulExtension` et
  `SegmentedResidualRole.UniqueResidualOccurrence` pour l’extension positive et
  l’unicité du résidu ;
- `AbstractSegmentedTurning.BoundaryGenerator`, `RegimeExit` et
  `UniformRegimeExit` pour distinguer génération, sortie et uniformité ;
- `StrongPerimetralTurning.History` et `RootedGeneratedHistory` pour les
  histoires proof-relevant ;
- `StrongPerimetralTurning.NormativeAdequacy` pour l’accord exact entre régime
  et norme autonome ;
- `StrongPerimetralTurning.perimeterDeployment`, les deux sens
  `requirementToOccurrence` / `occurrenceToRequirement` et leurs aller-retour
  pour l’individuation exacte du périmètre ;
- `StrongPerimetralTurning.oneStepAfterPerimeter` et
  `ConcreteContinuationAlgebra` pour une continuation positive effectivement
  construite ;
- `StrongPerimetralTurning.ExactHistoryInterpretation` pour le transport exact
  des occurrences vers une réalisation concrète, ainsi que
  `pullbackReadout` / `pushforwardReadout` pour reindexer une lecture sans lui
  attribuer de fidélité sémantique supplémentaire ;
- `StrongPerimetralTurning.History.OccurrenceReadout`, `perimeterReadout` et
  `occurrenceReadoutOfPerimeter` pour brancher les demandes d’univers, niveaux
  et autres observables **après** l’individuation des occurrences ; ces
  fonctions constituent un bus de réindexation exact, pas une sémantique ni une
  correspondance unique ou canonique par leur seul type ;
- `StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension`
  pour reconstruire exécutablement le facteur initial global depuis l’accord
  local exact ; dans cette structure, `realize_injective` est un théorème
  dérivé de `agreement` et ne doit pas être réintroduit comme donnée persistée ;
- `ConstitutiveAlignment.InjectiveMap` et `InjectiveMap.trans` pour la
  conservation des distinctions d’occurrences hors des situations où l’accord
  exact de `ExactNonClosingRealization` suffit déjà à les reconstruire ;
- les transports d’occurrences déjà prouvés dans le Cycle 1 ;
- `ConstitutiveAlignment.Separators.noFaithfulTerminalOnlyRealization` comme
  séparateur générique déjà acquis entre lecture terminale et réalisation fidèle.

`History.length` est une lecture numérique dérivée tardivement ; elle ne doit
jamais remplacer l’histoire ni servir à postuler sa hauteur avant construction.
Plus généralement, une lecture `OccurrenceReadout history Value` est une
fonction post-constitutive sur des identifiants déjà formés. Elle peut être
constante, non injective ou non numérique : toute propriété de fidélité,
d’adéquation ou de séparation des valeurs doit être prouvée séparément.

L’existence d’une `ExactHistoryInterpretation` établit une correspondance exacte
entre occurrences libres et concrètes. Elle ne rend pas cette correspondance
unique parmi toutes les bijections possibles. Lorsque l’identité canonique des
occurrences importe, le chantier doit utiliser l’interprétation construite par
le producteur concerné et son `occurrenceAgreement`, pas seulement l’existence
d’un bus inversible.

Pour les carriers hétérogènes du pipeline, une petite structure locale
est admise si l’encodage dans `History` exige une somme artificielle ou masque les
types. Cette structure doit alors être un adaptateur spécialisé, pas un nouveau
noyau concurrent.

Le noyau structurel ne doit être modifié que si une obligation concrète,
rencontrée dans une preuve ConLeche réelle, ne peut pas être exprimée par ses
interfaces actuelles. Toute extension doit rester générique et être justifiée
par un séparateur ou une factorisation positive, jamais par anticipation.

## 4. Portée exacte des résultats

### Démontré dans le dépôt Lean

- les relations de fidélité sont distinctes des fonctions de transformation ;
- leurs témoins se composent explicitement ;
- l’acceptation terminale ne permet pas de reconstruire une origine fidèle ;
- une substitution déterminée est rejetée par le certificat de fidélité ;
- un verdict peut être rapporté au source uniquement dans la portée transportée
  par les témoins disponibles.

### Recompilé séparément contre ConLeche épinglé

- la projection terminale `EnvModelM → TerminalSlice → no False` ;
- les séparateurs et factorisations δ ;
- l’analyse β indépendante et sa comparaison postérieure avec δ ;
- la fermeture du readback historique sur les branches `defn`, `thm`,
  `opaque` et `axiomSkip`, puis la factorisation de l'installation `propext`
  par les deux relations locales effectivement consommées ;
- le weakening de la première de ces relations : la membership terminale de
  `Iff.rec` et six faits sur les régimes des binders de son élimination à
  niveaux nuls suffisent à reconstruire « le `Iff` stocké force l'égalité » ;
- le raccord aux deux producteurs historiques réels de `Iff.rec`, modelé et
  natif : leurs runs d'inférence du type épinglé reconstruisent les six faits,
  lesquels sont ensuite préservés par toutes les branches de `DeclRun` et par
  le fold pur accepté depuis `Env.empty` ;
- le raccord cached correspondant : le vrai `InstallRun` de `FullyChecked`
  transporte directement `EnvWF` et `StoredIffRecBits`, y compris sur les deux
  voies inductives et les six blocs de base, sans appeler
  `fullyChecked_sound` ni construire `EnvModelM` ;
- le séparateur ι `.plain` jusqu’à l’échec relationnel de `headInPiR` ;
- l’affaiblissement compilé du front-door RHS de `indBottomPlain` : la lecture
  du type inféré et la membership du RHS ont été supprimées de sa prémisse
  sans modifier la conclusion ;
- la factorisation positive
  `InferReads + InferClaim → InferSubjectWellDenoted`, puis
  `run accepté + InferSubjectWellDenoted → PlainRhsFrontDoor`, ainsi qu’un
  séparateur montrant que `B0W` et une occurrence d’inférence réellement
  acceptée ne reconstruisent pas ce front-door ;
- un renforcement de ce séparateur au niveau exact d’un `IotaRuleRun` `.plain`
  complet : sélection de la règle, exécution de `iotaRecFueled`, théorème de
  continuation et toutes les obligations opérationnelles du run sont
  simultanément satisfaits, tandis que `PlainRhsFrontDoor` reste réfuté.
- une reconstruction du même contre-modèle sous la forme exacte imposée par
  `ProvisionRecsRun`, puis son relèvement, au même carburant, à
  `IotaRulesRun`, `IndRecsRun`, `DeclIndRun`, au `DeclRun` complet et enfin à
  l’égalité calculatoire réelle `checkDecl = .ok` ; l’atteignabilité de
  l’environnement synthétique depuis `Env.empty` n’est pas revendiquée.
- la réfutation formelle de cette atteignabilité exacte : tout
  `EnvModelM` sur l’ancienne base synthétique conduit à une contradiction, donc
  aucun `checkDeclsPure .verified` partant de `Env.empty` ne peut retourner cet
  environnement ;
- un test de remplacement atteignable, sans `sorry`, `native_decide` ni nouvelle
  déclaration `noncomputable` : `PUnit`, un alias accepté et une fonction
  acceptée produisent exactement l’environnement affaibli visé ; un vrai témoin
  `B0W` y existe, le vrai producteur ι de `PUnit.rec` s’exécute, et son minorant
  possède une lecture exacte mais non `WellDenoted`. Ce résultat localise
  toutefois la rupture **avant** la loi sémantique propre de ι. Un théorème
  positif complémentaire reconstruit le `PlainRhsFrontDoor` de la règle canonique
  `PUnit.rec` dans ce même témoin affaibli ;

Ces preuves appartiennent au checkout de dissection externe. Leurs empreintes et
leurs axiomes hérités sont rapportés dans les documents scientifiques ; elles ne
sont pas présentées comme des modules constructifs importés par le dépôt.

### Vérifié extérieurement

- un export précis du dépôt est soumis à une version précise de ConLeche ;
- le mode utilisé est `--verified` ;
- le verdict, le code de sortie, les versions et les empreintes sont enregistrés.

### Non revendiqué

- une preuve absolue de cohérence de Lean ;
- une preuve nouvelle de la correction de ConLeche ;
- une preuve de fidélité de tout le frontend de ConLeche ;
- une preuve que le binaire exécuté produit un terme Lean importable ;
- une équivalence sémantique complète entre le source Lean et le NDJSON ;
- une sécurité cryptographique ou matérielle de toute la chaîne ;
- une construction interne, uniforme en `k`, d’une tour d’univers arbitraire ;
- le fait qu’un flux syntaxique fini borne à lui seul toutes les valuations
  `ψ : Name → Nat` quantifiées par `EnvModelM` ;
- le remplacement actuel de `SetTheory.univChain` dans la preuve de
  `fullyChecked_sound` ;
- la minimalité absolue d’un invariant spécialisé pour `no False` ;
- l’atteignabilité depuis l’environnement initial de tous les séparateurs
  construits sur des témoins affaiblis ; l’ancien séparateur ι synthétique est
  désormais explicitement exclu de cette classe, tandis que le remplacement
  atteignable porte une obstruction sémantique antérieure à ι ;

## 5. Gate 0 — gel et compatibilité

### État vérifié

```text
dépôt testé : 794b8185abba13eb4ab91f77a7c87fd1cd2d6ae0
Lean du dépôt : v4.33.1 / 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
lean4export : 411dce7db58a3afc60ecab2d211acd1042b593dc
ConLeche : 86cd20a65660d757cedc81561a44579099b565d0
ConLeche construit avec Lean v4.33.0
```

La compatibilité pratique a été observée sur ce socle. Elle doit être vérifiée à
nouveau sur le commit scientifique final ; le run antérieur ne vaut pas gel du
résultat futur.

### Travaux

1. relever le commit exact du dépôt à auditer ;
2. relever un commit exact de ConLeche ;
3. relever un commit exact de `lean4export` ;
4. vérifier le format NDJSON attendu ;
5. déterminer si ConLeche accepte exactement un export Lean `v4.33.1` ;
6. vérifier la disponibilité des pins nécessaires au toolchain ;
7. conserver tous les clones et builds externes hors du dépôt ;
8. ne jamais rétrograder ou modifier le toolchain scientifique du dépôt pour
   satisfaire le checker externe.

### Fermeture

La Gate 0 est fermée si une combinaison épinglée exporteur/checker peut traiter
le toolchain exact du dépôt sans modification du noyau scientifique.

Si aucune combinaison compatible n’existe, consigner la limite et suspendre les
Gates 1 et 2. Ce résultat n’est pas un échec mathématique du dépôt.

**Statut :** fermée pour le socle testé ; à reconfirmer sur le commit final.

## 6. Gate 1 — audit externe minimal

### Préconditions

- Gate 0 fermée ;
- arbre Git propre ;
- commit à auditer identifié ;
- `lake build` réussi ;
- audits axiomatiques existants réussis ;
- manifeste vérifié.

Les racines candidates sont `StrongPerimetralTurning`, `Cycle2` et
`ConstitutiveAlignment`. Avant le run confirmatoire, vérifier leurs fermetures
d’imports et retenir la liste minimale qui couvre exactement les déclarations
publiées.

### Exécution canonique

```text
vérifier HEAD et l’absence de modification
  → lake clean
  → lake build
  → exécuter les audits internes
  → régénérer l’export depuis les racines publiées
  → calculer SHA-256 sur l’export
  → exécuter ConLeche --verified --jobs=1 sur ce fichier exact
  → recalculer SHA-256 sur le fichier après l’exécution
  → capturer verdict, stdout, stderr et code de sortie
```

Le script ne doit jamais lancer `--trusted` comme solution de repli.

Le run confirmatoire utilise `--jobs=1` pour stabiliser la procédure et ses
traces. Seuls le code de sortie `0` et la ligne `accepted N declarations`
constituent une acceptation couverte. Les codes `1`, `2` et `3`, ainsi qu’un
message d’épuisement mémoire, doivent être conservés sans réinterprétation.

### Métadonnées obligatoires

```text
commit du dépôt
état propre de l’arbre
toolchain Lean et hash correspondant
commit et commande de build de lean4export
commit et commande de build de ConLeche
commande d’export exacte
racines Lean exportées
hash SHA-256 de l’export
commande ConLeche exacte
mode verified et nombre de jobs
nombre de déclarations annoncé
verdict
code de sortie
horodatage UTC
```

### Statut du résultat

Le résultat est classé `vérifié extérieurement` et `observé`. Il n’est pas
classé `démontré dans Lean`.

Deux runs exploratoires ont accepté respectivement `63916` et `64359`
déclarations. Ils établissent la faisabilité du protocole, pas le résultat
confirmatoire du commit final.

Un `declined` doit être rapporté exactement comme une limite de couverture ou de
compatibilité de ConLeche. Il ne doit pas être renommé en rejet mathématique du
projet.

L’export contient des dépendances transitives du toolchain que ConLeche peut
accepter selon sa propre politique axiomatique. Son verdict ne remplace donc
jamais les `#print axioms` qui déterminent les dépendances effectives des
théorèmes principaux du dépôt.

## 7. Gate 2 — provenance exécutable de l’export

### Objectif

Lier effectivement le verdict au fichier régénéré pendant le même run, et non à
un hash copié ou à un artefact antérieur.

### Contrôles positifs

1. vérifier le commit attendu ;
2. vérifier la propreté de l’arbre ;
3. vérifier les sources contre le manifeste ;
4. régénérer l’export ;
5. calculer son hash ;
6. transmettre ce même chemin de fichier au checker ;
7. recalculer le hash du même fichier après le checker et exiger l’égalité ;
8. écrire le rapport seulement après le verdict et le second calcul ;
9. associer dans le rapport les deux hashes et le verdict de ce run unique.

### Mutations négatives

- commit différent ;
- arbre source modifié ;
- manifeste périmé ;
- export remplacé après calcul du hash ;
- hash attendu modifié ;
- racine Lean substituée ;
- commande d’export substituée ;
- version du checker substituée ;
- mode `--trusted` substitué à `--verified`.

Les mutations sont définies et figées avant le run confirmatoire.

### Limite

Cette gate atteste opérationnellement la liaison du run à ses octets et à son
commit dans le modèle de menace déclaré. Elle n’en fait pas un théorème Lean et
ne prouve pas la préservation sémantique de toutes les transformations du
frontend.

**Statut :** le script de provenance exécutable est implémenté ; son exécution
confirmatoire doit porter sur l’arbre final propre.

## 8. Gate 3 — noyau formel spécialisé du transport

### Fichier implémenté

```text
ConstitutiveAlignment/VerificationTransport.lean
```

### Interface minimale implémentée

```lean
structure VerificationPipeline where
  Source : Type
  Exported : Type
  Parsed : Type
  Presented : Type
  exportStep : Source → Exported
  parseStep : Exported → Parsed
  prepareStep : Parsed → Presented

def VerificationPipeline.run
    (pipeline : VerificationPipeline) :
    pipeline.Source → pipeline.Presented :=
  fun source =>
    pipeline.prepareStep (pipeline.parseStep (pipeline.exportStep source))
```

Cette signature est schématique : l’implémentation doit être polymorphe dans les
univers et reprendre le style du dépôt.

La fidélité n’est pas un champ automatique de `VerificationPipeline`.

Elle est portée séparément par des relations à valeurs dans `Type` :

```text
FaithfulExport source exported
FaithfulParse exported parsed
FaithfulPrepare parsed presented
```

Un `FaithfulRun source` rassemble uniquement les témoins correspondant aux trois
résultats réellement calculés par le pipeline.

L’objet `Presented` est la liste ou représentation effectivement soumise au
checker ; il n’est pas déjà un résultat vérifié. L’acceptation reste donc un
paramètre terminal indépendant :

```text
Accepted : Presented → Type
```

Le certificat source-relatif doit donc contenir les deux composantes sans les
identifier :

```text
FaithfulRun source
+
Accepted (pipeline.run source)
```

### Composition relationnelle minimale

Des relations arbitraires à valeurs dans `Type` ne se composent pas sans une
construction explicite. Employer une composition existentielle constructive :

```lean
def FaithfulComp
    (First : A → B → Type _)
    (Second : B → C → Type _)
    (source : A)
    (target : C) : Type _ :=
  Σ middle : B, First source middle × Second middle target
```

La chaîne complète conserve ainsi les occurrences intermédiaires au lieu de les
effacer. Si une relation doit conserver une détermination plus précise — nom,
type, énoncé, ordre ou identité d’occurrence — celle-ci apparaît dans son témoin.

Le champ abstrait `export` ne formalise pas à lui seul l’exécutable
`lean4export`. Une correspondance avec le run réel reste une observation de la
Gate 2 tant qu’un résultat supplémentaire ne l’a pas démontrée.

### Composition

La composition doit réutiliser `InjectiveMap.trans` lorsque la détermination
conservée est l’identité d’occurrences. Une relation plus riche est admise si la
transformation conserve autre chose qu’une injection, mais ce contenu doit être
explicite dans le type du témoin.

Lorsque la transformation est représentée par un accord exact de
`ExactNonClosingRealization`, l’injectivité doit être obtenue par le théorème
`realize_injective`, et non dupliquée comme hypothèse primitive. Les readouts ne
doivent intervenir qu’après cette constitution : ils annotent les occurrences
transportées, ils ne prouvent ni leur identité ni leur provenance.

### Fermeture

- module compilé ;
- aucun axiome ou principe interdit ;
- exactement un bloc `AXIOM_AUDIT` à la fin ;
- aucune duplication générale de `History` ;
- aucune définition de l’acceptation qui fabrique la fidélité.

Après fermeture, importer le module depuis `ConstitutiveAlignment.lean` et
ajouter uniquement ses déclarations capstones au bloc d’audit final de la
façade. Aucun nouveau root Lake n’est attendu.

**Statut :** fermé dans le dépôt ; toute extension doit préserver l’unique bloc
d’audit et la constructivité du module.

## 9. Gate 4 — séparateur constructif

### Objectif

Construire un pipeline substitutif dont l’objet présenté est accepté, tout en
réfutant constructivement le témoin de fidélité requis.

### Réemploi

Le séparateur doit être raccordé à
`noFaithfulTerminalOnlyRealization`. Il ne doit pas redémontrer sous un autre nom
le seul fait qu’une fonction constante n’est pas injective.

### Résultats minimaux

```text
acceptedPresentation
substitutedRun_hasNoFaithfulOrigin
presentationAcceptance_doesNotDetermineOrigin
faithfulRun_preservesDeclaredOccurrence
```

Le théorème négatif doit construire une fonction vers `False`; il ne doit pas
reposer sur une négation classique ou une décision externe.

### Fermeture

Un cas fidèle et un cas substitutif compilent, sont audités, et exposent la même
notion d’acceptation de l’objet présenté sans exposer le même certificat de
provenance.

**Statut :** fermé dans la portée locale annoncée.

## 9b. Gate 4b — alignement interne de ConLeche

### Objet

Traiter explicitement le résultat principal de ConLeche comme une relation
d’alignement sur le même candidat `(entrée, environnement)` :

```text
R = checkDecls .verified entrée = .ok environnement
S = l’environnement ne contient aucune constante de type False
```

Le résultat externe fournit `R → S`. Il ne fournit ni `S → R`, ni la fidélité
du chemin `SOURCE → PRESENTED`.

### Test formel local

1. représenter un checker par son calcul opérationnel et sa norme sémantique ;
2. définir séparément soundness `R → S`, completeness `S → R` et adéquation ;
3. factoriser soundness en `R → certificat → S` afin de rendre visibles les
   relations constitutives intermédiaires ;
4. composer fidélité amont, acceptation et soundness sans les identifier ;
5. fermer trois séparateurs constructifs :
   - l’acceptation seule ne produit pas `S` ;
   - soundness ne produit pas completeness ;
   - soundness, acceptation et `S` ne reconstruisent pas la provenance.

La reconstruction locale reproduit la forme du contrat public de ConLeche ;
elle n’importe pas son code et ne revendique pas un nouveau théorème sur son
implémentation.

**Statut :** fermé pour le modèle local ; la dissection du code réel relève de
la Gate 5b.

## 10. Gate 5 — cas d’étude ConLeche réel

### Gate 5a — provenance et transport externe

Le cas local de transformation du frontend est fermé dans la portée documentée :
un cas fidèle, une substitution non fidèle et le rejet constructif de cette
substitution sont raccordés au noyau de transport. Cela ne prouve pas la fidélité
de tout `lean4export`, du parser ou du frontend de ConLeche.

Le transport négatif relatif à `no False` conserve deux obligations séparées :

```text
couverture des occurrences pertinentes
+
préservation des contre-exemples
→
no False présenté → no False source
```

Les séparateurs montrent que, dans la famille testée, aucune des deux capacités
ne peut être simplement supprimée. Il s’agit d’une suffisance factorisée et de
nécessités locales par séparateurs, pas d’une minimalité absolue.

### Gate 5b — dissection interne de la garantie `no False`

#### Cartographie exacte

```text
Cᵗ = EnvModelM
     fournisseur sémantique riche

Cʷ = EnvModelOk
     invariant effectivement transporté par le fold

A  = TerminalSlice
     slice terminale suffisante

B0W
   = témoin affaibli initial
     composé de la slice et de la fermeture eta
```

Le capstone lit seulement une projection de `EnvModelM` vers `base2`,
`type_reads` et `mem_type`. Cela démontre une suffisance terminale. Cela ne
montre pas que les autres champs sont inutiles à la construction inductive du
modèle.

Le noyau générique stabilisé distingue :

```text
WitnessCandidate      témoin initial + extraction terminale
ShadowCarrier         oubli propositionnel par Nonempty
WeaklyStable          existence d’un successeur
HistoricalStable      successeur construit et relié à l’ancien témoin
TransitionObligation  donnée consommée par une transition
LocallyReconstructs   reconstruction depuis témoin ancien + pas
Separator             contre-exemple concret indexé par un pas
```

Il établit seulement les directions constructives acquises, notamment
`shadowExtract`, `HistoricalStable → WeaklyStable` et la réfutation d’une
reconstruction locale par un séparateur. Il n’affirme ni converse, ni fermeture
canonique, ni minimalité.

#### État gelé de δ et β

δ est le cas de référence gelé au commit `d296630`. L’audit a extrait une seed
indexée par l’occurrence réellement dépliée, puis sa projection vers une
préservation des appartenances gardée par `Sat`.

β a été développé indépendamment. La comparaison postérieure au commit
`e567f09` établit que son transport sémantique intermédiaire coïncide, à indices
égaux, avec cette préservation gardée. Le statut exact est :

```text
AdmissibleDeltaSeed
        ↓ strictement dans la classe abstraite testée
GuardedMembershipPreservation
        ≡
BetaMembershipTransport
```

Dans la classe des sorties réellement constituées par `AcvalDefnInst`, le
producteur δ construit toujours la seed plus riche avant sa projection. Il faut
donc distinguer :

```text
constitution  ≠  exportation  ≠  consommation
```

et distinguer également l’ordre logique entre capacités de l’ordre relatif aux
objets effectivement productibles.

#### État ouvert de ι

L’analyse ι est indépendante et ne doit pas importer la capacité commune δ/β
avant son propre gel. La branche `.plain` possède un séparateur réel : la règle
est sélectionnée, `iotaRecFueled` s’exécute, la continuation est certifiée et les
deux constituants du RHS sont bien dénotés, mais leur composition échoue déjà
sur la clause relationnelle `headInPiR`.

Le chemin positif du producteur `.plain` a maintenant été affaibli séparément.
Une recompilation temporaire du vrai `indBottomPlain`, ensuite restauré
bit-pour-bit, montre que son front-door RHS ne consomme ni le témoin de lecture
du type inféré ni la membership du RHS dans ce type. Il consomme exactement :

```text
∀ ψ, ∃ Ra,
  denoteMeta rhs = some Ra
  ∧ ∀ ρ, WellDenotedV ρ Ra
```

La production de cette interface se factorise sans conserver le type inféré :

```text
InferReads + InferClaim
        ↓ projection
InferSubjectWellDenoted

run d’inférence accepté + lecture opérationnelle
+ InferSubjectWellDenoted
        ↓
PlainRhsFrontDoor
```

Un second séparateur, fondé sur une application effectivement acceptée par
`inferTypeCore`, montre d’abord que `B0W + run RHS accepté` ne suffit pas à
reconstruire `PlainRhsFrontDoor`. Ce résultat isole la coupure sémantique après
l’acceptation opérationnelle. Il a depuis été renforcé par un contre-modèle qui
satisfait toutes les obligations d’un `IotaRuleRun` `.plain` complet, puis par
une reconstruction qui respecte exactement la forme d’environnement imposée
par `ProvisionRecsRun` et traverse le fold d’installation inductif complet.

La descente dans la branche application de `InferSubjectWellDenoted` a ensuite
isolé, sans employer l’interface commune δ/β, le premier résidu relationnel
positif :

```text
PlainMembershipTransport context before after :=
  ∀ ρ, Sat context ρ →
  ∀ x, x ∈ interp before → x ∈ interp after
```

Pour cette analyse indépendante :

```text
égalité sémantique gardée
        ↓ strictement
PlainMembershipTransport
        ↓ avec la membership inférée de la tête
headInPiR sur la lecture exacte du whnf
```

La stricte faiblesse est non vacue : `Sort 0 → Sort 1` transporte au moins
`empty`, alors que l’égalité de leurs interprétations implique une
self-membership impossible. Sur le contre-modèle applicatif accepté, le même
`whnf`, la même lecture source et la même lecture réduite ne reconstruisent pas
`PlainMembershipTransport`, car celle-ci produirait exactement le
`headInPiR` déjà réfuté. Tous ces raccords compilent ; leurs `#print axioms`
rapportent uniquement les axiomes hérités de ConLeche (`propext`,
`Classical.choice`, `Quot.sound`).

Sur ce même témoin, les deux autres clauses du frame sont maintenant prouvées
positivement : la lecture de l’argument appartient au domaine `Sort 0`, et la
condition de niveau zéro est vacue parce que `pwBit .never = 1`. Le séparateur
courant est donc entièrement localisé sur `headInPiR`.

Un second contre-modèle applicatif accepté a ensuite testé indépendamment la
membership de l’argument. Il construit un environnement `B0W` où :

```text
lecture exacte de l’application                    ✓
run inferTypeCore réellement accepté               ✓
WellDenoted de la tête et de l’argument             ✓
transport de la tête (identité)                     ✓
headInPiR sur un domaine vide                       ✓
condition de niveau zéro                            ✓
membership de l’argument dans le domaine vide       ✗
```

La nouvelle coupure n’exige pas une seconde forme de capacité : elle réutilise
exactement `PlainMembershipTransport`, cette fois entre la lecture du type
inféré de l’argument et la lecture du domaine du `forall`. Le transport est
réfuté constructivement parce que l’argument appartient à son univers inféré
mais ne peut appartenir au domaine vide. Ainsi, dans la preuve positive de
`infer_app_claim`, la même relation gardée intervient déjà à deux raccords
distincts :

```text
type inféré de la tête → whnf fonctionnel
type inféré de l’argument → domaine du forall
```

Le second séparateur compile et son audit d’axiomes rapporte seulement les
axiomes hérités de ConLeche. Sa portée reste celle d’une occurrence d’inference
acceptée, pas encore celle d’un `IotaRuleRun` d’installation complet.

Le test générique de la condition de niveau zéro ne produit pas un troisième
séparateur. Il révèle au contraire que cette condition, bien que consommée par
la preuve canonique de `sound_app`, peut être éliminée du front-door RHS
affaibli. La distinction décisive est la suivante :

```text
sortie complète de infer_app_claim
  = WellDenotedV de l’application
  + membership dans le type résultat exact

front-door RHS .plain
  = WellDenotedV de l’application seulement
```

Pour la seconde cible, si le niveau du frame est positif, la condition zéro
est vacue. S’il vaut zéro, `headInPiR` identifie la tête au point de preuve
canonique ; on reconstruit alors constructivement un autre frame propositionnel
ayant pour domaine le singleton de l’argument courant et pour fibres
`unitSet`. Ce frame suffit à `WellDenoted_app`, sans préserver l’identité du
frame opérationnel ni sa condition de fibre. `AnnotValid_app` ne consomme de
son côté que les validités des deux constituants.

Trois théorèmes compilés enregistrent cette réduction :

```text
WellDenoted head + WellDenoted argument
+ headInPi + argumentInDomain
  → WellDenoted (app head argument)

la même factorisation à la monnaie WellDenotedV

les deux PlainMembershipTransport
+ les memberships sources exactes
+ les WellDenotedV des constituants
  → WellDenotedV de l’application
```

Cette élimination est propre à la consommation terminale affaiblie. Elle ne
montre pas que la condition zéro est inutile pour produire la membership de
l’application dans son type résultat exact : cette seconde conclusion de
`sound_app` continue à la consommer.

Le premier sens du raccord au producteur complet est également formalisé. Un
`IotaRuleRun` dont la règle installée est `.plain` projette constructivement
vers une occurrence RHS contenant exactement :

```text
gardes de fermeture et de portée du RHS source
annotation acceptée vers le RHS installé
gardes correspondantes du RHS annoté
run inferTypeCore accepté sur ce même RHS
identité du RHS installé
mode .plain
```

Cette projection ne consomme aucun modèle sémantique. Elle établit :

```text
IotaRuleRun complet → occurrence RHS acceptée
```

Le raccord négatif au niveau projeté est explicite et compilé. Le contre-modèle
applicatif fournit, pour un même fuel choisi constructivement par maximum,
l’annotation et l’inférence acceptées exigées par cette occurrence, tout en
réfutant son `PlainRhsFrontDoor`. Ainsi :

```text
B0W + occurrence RHS acceptée ↛ PlainRhsFrontDoor
```

Le raccord a ensuite été fermé au niveau du producteur local complet. Un
environnement de base synthétique sélectionne la règle `.plain`, un même
environnement propre fournit le témoin `B0W`, et toutes les composantes du vrai
`IotaRuleRun` sont construites, notamment `iotaRecFueled`, le théorème de règle
et le certificat de continuation. Pourtant, le RHS installé garde exactement la
lecture applicative séparatrice et son `PlainRhsFrontDoor` conduit à `False` :

```text
B0W + IotaRuleRun complet ↛ PlainRhsFrontDoor
```

Les deux théorèmes de ce raccord compilent et leur `#print axioms` rapporte
uniquement les axiomes hérités du développement ConLeche (`propext`,
`Classical.choice`, `Quot.sound`), sans `sorryAx`.

Le pli de liste immédiatement supérieur n’ajoute aucune réparation : le même
témoin se relève constructivement en un `IotaRulesRun` complet à une seule
règle, avec la même réfutation du front-door. Son audit d’axiomes donne le même
résultat hérité. La première contrainte productrice réellement nouvelle est
donc `ProvisionRecsRun`, pas `IotaRulesRun`.

Le premier couple d’environnements synthétique ne pouvait pas être réutilisé à
ce niveau : un lemme compilé montrait qu’aucune liste de recursors ne pouvait le
relier par `ProvisionRecsRun`. Cette obstruction a été respectée, non contournée.
Le contre-modèle a été reconstruit depuis une nouvelle base où le provisionneur
préfixe réellement le `recInfo` à règles vides exigé. La base contient un
recursor modèle qui est une véritable fonction sémantique vers `empty`; le RHS
séparateur possède la même interprétation terminale sans posséder la structure
`WellDenoted` requise. Cela permet simultanément :

```text
ProvisionRecsRun au carburant F
+ IotaRulesRun au même carburant F
+ IndRecsRun
+ DeclIndRun
+ DeclRun avec DeclIndRunDispatch
+ B0W sur l’environnement provisionné
+ négation de PlainRhsFrontDoor pour la règle installée
```

Les raccords de carburant utilisent les lemmes de monotonie réels du checker ;
aucun indice, environnement ou RHS indépendant n’est substitué. Le théorème
final conserve explicitement le provisionnement et le fold de règles dans son
énoncé afin que l’échec sémantique porte sur la règle installée par ce même run.
Les `#print axioms` rapportent seulement `propext`, `Classical.choice` et
`Quot.sound`, hérités du développement ConLeche, sans `sorryAx`.

Le converse général `DeclRun → checkDecl = .ok` n’est toujours pas revendiqué.
En revanche, il est désormais prouvé **pour ce témoin concret** par une
reconstruction noyau de chaque calcul : `IotaRuleRun → checkIotaRule`, fold de
la liste de règles, provision des recursors, `checkIndRecs`, `checkModeled`, puis
`checkDecl`. Le théorème final rassemble, aux mêmes indices, l’égalité
`checkDecl = .ok`, le provisionnement, le fold de règles et la négation du
front-door sémantique du RHS installé. Une sonde initiale par `native_decide` a
été retirée ; les `#print axioms` finaux ne rapportent aucun axiome généré ni
`sorryAx`, seulement `propext`, `Classical.choice` et `Quot.sound` hérités de
ConLeche.

Cette fermeture reste locale à un environnement de base synthétique fourni au
checker. La question de son atteignabilité exacte est maintenant **fermée
négativement** : les lectures de l’alias et du recursor modèle imposées par
`defn_reads`, combinées à `mem_type`, forceraient `univ 0` à appartenir à un
`piR` positif, ce qui est contradictoire. Par `checkDeclsPure_sound_of`, aucune
liste acceptée depuis `Env.empty` ne peut donc retourner cet environnement
exact. Cette preuve ne repose ni sur un échec de recherche ni sur une
énumération de programmes.

Les certificats correspondants sont isolés dans le checkout de dissection :

- `ScratchIotaPlainReachability.lean` ferme l’improductibilité de l’ancienne
  base exacte ;
- `ScratchIotaPlainReachableProbe.lean` reconstruit sans oracle le préfixe
  accepté ;
- `ScratchIotaPlainReachable.lean` construit le témoin affaibli, le pas ι réel,
  l’échec du minorant, son raccord à la capacité δ/β existante et le front-door
  positif de la règle canonique ;
- `ScratchB0ReachableDefn.lean` revient au résidu de définition : il construit
  un vrai `DeclDefnRun` après le préfixe accepté, démontre l’échec de
  `DefnValueWellDenotedObligation`, factorise positivement cette obligation par
  la capacité commune, puis démontre que le checker accepte aussi le préfixe
  étendu contenant cette définition ; `reachableCheckerDefnSeparator` rassemble
  ces faits au même carburant et sur le même témoin ;
- `ScratchDeltaHistoricalCandidate.lean` teste, sans créer `B1`, la fermeture
  de la capacité commune sur les occurrences δ admissibles. La candidate
  `AdmissibleDeltaMembershipProvider` est produite par
  `AcvalDefnReadableSeed`, donc par `AcvalDefnInst`, suffit à reconstruire le
  premier résidu `Pdenote`, et est constructivement réfutée sur le témoin
  atteignable affaibli ;
- `ScratchDeltaProviderStability.lean` effectue le premier test de conservation
  de cette candidate depuis l’état initial. La capacité est vacuement présente
  dans l’environnement vide, le checker accepte réellement comme première
  déclaration l’alias fonctionnel, et il existe sur l’environnement obtenu un
  `B0W` terminalement valide qui réfute la candidate. Ce séparateur démontre
  que les seules données terminales du successeur ne **forcent** pas le
  provider. Il ne réfute pas une stabilité faible autorisée à choisir une autre
  réalisation successeur. Le même fichier descend ensuite d’un étage : deux
  lectures exactes identiques du nouveau corps produisent positivement la
  `ReadableDeltaSeed` déjà isolée, tandis que le successeur terminal incohérent
  réfute cette seed sur les lectures exactes de la nouvelle tête et de son corps.
- `ScratchDeltaOldDefinitionReuse.lean` teste la première définition ancienne
  sous un argument introduit par une seconde déclaration réellement acceptée.
  Le fichier construit le fold de deux définitions depuis `Env.empty`, un
  `TerminalSlice` et un `WalkCarrier` aux deux états, puis isole l’échec du
  contexte ouvert portant l’annotation historique exacte du type déclaré. Il
  ferme immédiatement le weakening requis : le même argument sémantique `pt`
  possède un représentant ouvert admissible à `Sort 1`. Le séparateur de
  l’annotation exacte n’établit donc ni une nécessité de persistance de
  `WellDenotedV`, ni un échec de stabilité du provider. Le même fichier ferme
  ensuite la factorisation positive : l’ancien provider transporte
  l’application ouverte, sa spécialisation à `pt` donne l’application fermée
  à `.prf`, et les deux invariances de valuation restantes se déduisent de la
  closedness par lift déjà présente dans `EnvModel`. Le cas concret du nouvel
  argument est donc reconstructible localement. Le weakening est maintenant
  raccordé au producteur du représentant : pour tout `ValueFrontRun`, les seules
  instances locales `InferReads` et `InferClaim` reconstruisent le type inféré
  effectivement lu, sa validité `WellDenotedV`, la lecture de la valeur et son
  appartenance à ce type. Ni `DefEqClaim`, ni `ConstantValRun`, ni le type déclaré
  n’interviennent. Ce résultat ne remet aucune théorie globale dans le carrier ;
  il localise exactement ce que la future preuve de conservation devra produire
  au site d’introduction de l’argument.

Le séparateur du premier successeur est également classé au niveau historique.
Il existe maintenant un successeur alternatif construit sur le même vrai
`DeclDefnRun` qui choisit pour l’alias la lecture exacte de son corps et porte à
la fois un `WalkWitness` et le provider δ. Ainsi :

```text
successeur terminal arbitraire
  peut perdre le provider

mais

construction exacte du successeur
  → WalkWitness + provider
```

Les deux premières étapes historiques concrètes sont donc positivement fermées.
Pour la seconde, la preuve distingue explicitement la tête fraîche et l’alias
retenu, puis reconstruit leurs seeds depuis les lectures exactes de leurs corps
stockés. Le prochain test ne doit plus rechercher un contre-modèle sur cette
chaîne déjà fermée ; il doit isoler le premier résidu de la conservation
**générique** du provider sous une déclaration `defn`, sans convertir les
égalités exactes utilisées par ce témoin concret en champs persistants.

Le premier test générique élimine déjà une fausse obstruction. Une
`ReadableDeltaSeed` dont les deux lectures sont indépendantes de la valuation
remonte, à **toute profondeur**, vers la seed sémantique universelle : le terme
`.fvar depth` se lit comme `.bvar 0` et permet de tester un argument sémantique
arbitraire. Elle peut donc être recontextualisée dans n’importe quel nouvel
environnement de lecture. L’apparition de nouveaux arguments lisibles après un
cons ne force aucune mémoire supplémentaire. Le résidu suivant est plus bas :
pour réutiliser le producer ancien, il faut raccorder la lecture d’un corps
stocké dans l’ancien environnement à sa lecture dans le successeur. Cette
disponibilité doit maintenant être cherchée dans l’histoire d’acceptation ou
reconstruite localement ; elle ne doit pas être remplacée par `defn_reads`
entier sans séparateur.

La factorisation du résidu est également compilée. Dès qu’une lecture ancienne
du corps est disponible, `denoteMeta_cons_mono` la transporte dans le vrai cons,
l’injectivité de `Option.some` l’identifie à toute lecture successeur du même
corps, puis la seed ancienne se recontextualise. Ainsi, ni l’égalité complète
entre feuille de constante et corps, ni `AcvalDefnInst` ne sont nécessaires à
ce raccord. Le seul témoin encore absent est l’existence de la lecture ancienne
elle-même. Sa reconstruction doit maintenant être testée depuis `EnvWF`, le run
d’installation historiquement disponible ou une trace constituée ; son absence
de la signature courante ne constitue pas encore une preuve de nécessité.

Le run réel ferme désormais le côté frais sans hypothèse supplémentaire.
`ValueFrontRun.annotatedValueReadable` construit une lecture de la valeur
annotée à toute instanciation de niveaux et toute profondeur ; le vrai cons la
transporte et `acvalWith_self` l’identifie à la tête installée. En parallèle,
l’obligation propositionnelle exacte `StoredDefnBodiesReadable` est vide à
l’origine et se préserve sous un cons `defn` : le corps frais vient du run, les
corps retenus viennent de leurs lectures préfixes. Enfin,
`AcvalDefnReadableSeed.consDefn_of_bodyReadability` montre que cette seule
obligation, jointe au producteur δ affaibli précédent, suffit à préserver ce
producteur. C’est une preuve de suffisance pour la branche ; ce n’est toujours
pas une preuve que l’obligation doit appartenir au carrier final.

Le test négatif de `EnvWF` est maintenant lui aussi construit. Un environnement
singleton bien formé et muni d’une `TerminalSlice` peut stocker comme corps un
`letE`, alors que `denoteMeta` refuse structurellement cette forme. Il fournit
donc un séparateur concret contre
`TerminalSlice + EnvWF → StoredDefnBodiesReadable`. Cependant le même fichier
prouve que ce corps ne peut être la sortie annotée d’aucun `ValueFrontRun` : le
théorème opérationnel `acceptedReads_of` donnerait une lecture, contradictoire
avec la clause `letE`. Le séparateur arbitraire est ainsi exclu de la classe
productible par une transition `defn` réelle. Il ne peut pas justifier une
persistance ; le prochain raccord doit transporter cette exclusion le long de
l’histoire complète du fold.

Ces six fichiers compilent sans `sorry`, `native_decide` ni nouvelle
déclaration `noncomputable`. Leurs `#print axioms` ne rapportent que
`propext`, `Classical.choice` et `Quot.sound`, hérités de ConLeche.

Un remplacement atteignable a ensuite été construit sans réintroduire
l’infrastructure globale dans le carrier affaibli. Le vrai checker accepte
successivement le bloc `PUnit`, l’alias fonctionnel et la fonction ; le fold
retourne exactement l’environnement annoncé. Sur ce même environnement, un
témoin `B0W` incohérent mais terminalement suffisant existe sous `Nonempty`, et
le vrai `PUnit.rec` effectue son pas ι canonique. Le minorant fourni à cette
occurrence est lu comme
`PUnit PUnit` et n’est pas `WellDenoted` parce que sa tête n’appartient à aucun
`piR`. En revanche, le `PlainRhsFrontDoor` du RHS stocké de la règle canonique
`PUnit.rec` est constructivement reconstruit dans ce même témoin. Le test sépare
donc positivement la loi de règle ι de l’obstruction déjà présente dans son
minorant.

Ce remplacement **ne transporte pas** la conclusion du séparateur synthétique
vers la classe atteignable. Il montre au contraire que la rupture est déjà
présente dans une entrée du recursor, avant la loi sémantique propre de ι. Il
faut donc distinguer explicitement :

```text
ancien témoin synthétique
  → loi RHS .plain réfutée
  → environnement exact improductible depuis Env.empty

remplacement atteignable
  → vrai préfixe accepté + vrai pas PUnit ι
  → minorant déjà non WellDenoted
  → PlainRhsFrontDoor de la loi RHS canonique reconstruit positivement
```

La convergence observée sur le minorant n’est pas comptée comme un résultat
propre à ι : elle localise une obstruction antérieure, déjà expliquée par δ.
Le retour au résidu `defn` ferme maintenant les étapes suivantes de la méthode :

```text
résidu concret sur une définition acceptée                    ✓
factorisation positive par GuardedMembershipPreservation      ✓
weakening antérieur jusqu’à cette capacité commune             ✓
séparateur constructif contre sa reconstruction depuis B0W     ✓
atteignabilité de l’état et de la transition par le checker    ✓
atteignabilité historique du témoin affaibli lui-même          non revendiquée
```

Le prochain travail n’est ni ι ni `B1`. Il consiste à remonter le producteur
positif déjà établi de cette capacité et à déterminer la plus faible donnée
historique qui permet de la reconstruire lors de toute occurrence δ pertinente.
L’interface globale `AcvalDefnReadableSeed` est seulement une enveloppe
suffisante connue ; elle ne doit pas être ajoutée telle quelle au carrier sans
affaiblissement. La seed indexée par l’occurrence reste une obligation locale,
pas encore une donnée persistante.

Un premier affaiblissement producteur est maintenant compilé :

```text
AcvalDefnInst
  → AcvalDefnReadableSeed
  → AdmissibleDeltaMembershipProvider
  → GuardedMembershipPreservation sur l’occurrence réelle
  → Pdenote
```

Le séparateur atteignable réfute `AdmissibleDeltaMembershipProvider` sur le
témoin affaibli. Ce résultat force une mémoire supplémentaire relativement à
ce témoin, mais ne prouve pas encore que cette candidate est stable, minimale
ou qu’elle doit être stockée telle quelle. Elle reste donc explicitement hors
de tout carrier nommé `B1`.

Le premier test de conservation ajoute une frontière plus précise :

```text
B0W initial + provider initial + vraie transition defn
  → il existe un successeur B0W terminalement valide sans provider
```

La candidate ne descend donc pas automatiquement avec une réalisation
terminale arbitraire. Cette conclusion ne vaut pas encore
`WeaklyStable → False`, car une preuve de stabilité faible peut choisir un
autre successeur. Le prochain résidu est la relation de compatibilité qui doit
relier le témoin ancien au témoin nouveau et exclure cette substitution de
réalisation. Cette relation doit être extraite de la construction positive du
successeur ; elle ne doit pas être définie en encapsulant directement le
provider.

La première compatibilité effectivement extraite n’est pas une nouvelle
abstraction : c’est la `ReadableDeltaSeed` existante, appliquée seulement à la
nouvelle tête et au corps stocké de cette transition. La factorisation et son
séparateur sont maintenant compilés :

```text
deux lectures exactes du même corps
  → identité des lectures
  → ReadableDeltaSeed de la nouvelle tête vers le corps

successeur B0W terminal incohérent
  → lectures exactes de la tête et du corps
  → ¬ ReadableDeltaSeed
```

Cette seed est encore une obligation locale de compatibilité du successeur.
Elle n’est ni un champ persistant ni une preuve générale de fermeture du
provider. Sa suffisance sur la première transition est maintenant démontrée :
comme l’environnement successeur ne contient que la définition fraîche, une
famille de seeds tête/corps fraîches reconstruit `AcvalDefnReadableSeed`, puis
le provider complet. Le prochain test doit exposer séparément ce qui manque
lorsque des définitions anciennes sont réemployées sous de nouveaux arguments
après une transition ultérieure.

Ce premier test est désormais exécuté sur une chaîne réellement acceptée. La
route naïve conserve l’annotation exacte du type stocké :

```text
B0W ancien + seconde définition acceptée
  → type déclaré lu et habité
  ↛ CtxOk du fvar portant exactement ce type
```

La méthode interdit d’en conclure que `WellDenotedV` doit être persisté. Le
weakening positif montre en effet :

```text
même valeur sémantique pt
  → représentant ouvert typé Sort 1
  → CtxOk valide + appartenance à univ 1
```

Le premier séparateur ne réfute donc qu’une représentation historique précise,
pas toute reconstruction locale du transport. Pour le nouvel argument concret
`.prf`, le raccord du provider ancien à l’application fermée est maintenant
construit par le représentant alternatif. Aucune mémoire supplémentaire n’est
forcée à cet étage.

Le provider entier est maintenant fermé sur la chaîne concrète de deux
définitions : la tête fraîche reçoit la lecture exacte de sa lambda stockée et
l’alias ancien conserve la lecture exacte de son `forall`; ces deux identités
locales suffisent à reconstruire toutes les occurrences delta de
`freshArgumentEnv`. Le résultat ne vaut pas encore conservation générique : il
choisit une réalisation exacte particulière et exploite que l’environnement
final contient précisément ces deux définitions. Le prochain résidu est donc
la factorisation d’une transition `defn` arbitraire à partir d’un ancien témoin
déterminé. Tant que le premier échec de cette factorisation n’est pas isolé et
séparé, aucune capacité supplémentaire ne peut entrer dans le carrier.

La première factorisation générique est maintenant acquise dans
`ScratchDeltaProviderGeneric.lean` : la fermeture applicative lisible ne se
fragilise pas lorsque le contexte de lecture grandit. Pour des lectures fermées,
elle est déjà universelle à la profondeur du producteur et se restreint ensuite
constructivement au nouveau contexte. Le premier résidu générique n’est donc
pas le transport des futurs arguments, mais le **readback du corps ancien** :
obtenir, depuis l’histoire constituée, une lecture ancienne concordant avec la
lecture du même corps dans le successeur. Ce résidu reste transitionnel ; aucune
preuve n’établit encore qu’il doit être persisté.

Le lemme suivant ferme la partie positive du readback :

```text
ancienne seed + ancienne lecture du corps
+ cons frais réel + lecture successeur du même corps
→ identification des lectures
→ seed recontextualisée dans le successeur
```

Le prochain test porte donc uniquement sur la production de l’ancienne lecture
du corps. Il doit d’abord essayer `EnvWF` et les certificats historiques déjà
constitués. Un champ de type `defn_reads`, même affaibli à l’existence, reste
interdit tant qu’un séparateur atteignable n’a pas exclu ces reconstructions.

La frontière positive est maintenant fermée sur un vrai cons `defn` : le
couple formé du producteur δ affaibli et de l’existence propositionnelle des
lectures de corps se conserve. Le problème restant n’est plus la suffisance de
ce couple, mais le statut de sa seconde composante : conséquence de `EnvWF`,
information reconstructible depuis l’histoire, ou mémoire effectivement
nécessaire. Seuls les prochains séparateurs et leur test d’atteignabilité
peuvent trancher entre ces statuts.

Le premier raccord à l’histoire complète est maintenant compilé dans
`ScratchDeltaFoldHistory.lean`, avec deux statuts volontairement séparés.
D’une part, `AcvalDefnInst` implique `StoredDefnBodiesReadable`, donc tout
témoin produit par le fold riche et tout environnement accepté par
`checkDeclsPure` possède une base sémantique satisfaisant ce résidu. Cette
projection réutilise explicitement `EnvModelM.defn_reads` : elle exclut le
séparateur illisible de la classe riche productible, mais ne ferme pas la
réduction spécialisée. D’autre part, indépendamment du carrier riche, tout
`coreCons` frais qui n’installe pas une définition conserve les lectures des
anciens corps par crossing monotone. Le raccord est fermé pour une vraie
branche `thm` : le support local déjà isolé construit la même `TerminalSlice`
successeur, et la lisibilité des corps suit sans `EnvModelM`, `defn_reads` ni
égalité tête/corps. Le même raccord est maintenant fermé séparément pour une
vraie branche `opaque`; son certificat optionnel de réduction n’est pas
consommé par le readback. Ainsi, à cet étage, ces deux déclarations non
définitionnelles n’ajoutent aucune nouvelle obligation de lecture des corps ;
elles transportent seulement l’information historiquement produite par les
déclarations `defn` antérieures.

La sous-branche `axiomSkip`, qui ne modifie pas l’environnement, est également
fermée par conservation littérale des deux témoins. Pour les trois branches
d’axiome qui installent une tête, le lemme générique montre déjà que la
lisibilité des anciens corps suivra dès que leur `TerminalSlice` successeur sera
construite. Le premier résidu n’est donc plus le readback : il se situe dans la
construction positive de cette slice, notamment dans l’appartenance de la
nouvelle feuille axiomatique à la lecture de son type. Ce résidu appartient à
l’audit de la branche `axiom`; il doit être factorisé puis séparé avant de
poursuivre vers `basis` ou `ind`.

Ce résultat ne justifie toujours pas un champ persistant. La prochaine étape
doit ouvrir seulement la première branche axiomatique installante et isoler les
données exactes nécessaires à sa nouvelle ligne de membership. Un recours
direct à `EnvModelM.storedDefnBodiesReadable` ou aux théorèmes riches
`axiomStd`/`axiomTrustCompiler`/`axiomOfReduce` à cet endroit ne compterait que
comme contrôle de suffisance riche, pas comme fermeture du candidat affaibli.

La première branche installante, `propext`, possède maintenant sa factorisation
positive exacte dans `ScratchDeltaFoldHistory.lean`. Le vrai
`ConstantValRun`, le pin `propext`, les lectures du type stocké et les trois bits
de produits reconstruisent toute la nouvelle ligne terminale dès que deux
relations locales sont fournies sur la même réalisation :

```text
Iff stocké force A = B

Eq stocké, à l'instance u := 1,
se lit comme eqv A B
```

Ces deux relations suffisent à construire l'appartenance de la feuille
canonique `propext` à la lecture exacte de son type, puis la même
`TerminalSlice` successeur et la conservation des lectures de corps. Les deux
projections depuis `EnvModelM` ont été recompilées uniquement comme contrôle :
elles confirment que la factorisation affaiblie conserve exactement les indices
de la preuve riche, mais elles ne sont pas utilisées comme fermeture du
carrier spécialisé.

Le weakening de la première relation a d'abord été poursuivi séparément dans
`ScratchPropextIffWeakening.lean`. Une première preuve positive supprimait la
théorie globale des types validés et ne conservait que l'`AnnotValid` de la
lecture exacte du seul type stocké de `Iff.rec` à la valuation de niveaux
nulle. Cette frontière était encore trop forte.

`ScratchPropextProducer.lean` descend maintenant sous cet `AnnotValid`. La
preuve d'élimination du recursor consomme exactement six faits de régime : les
cinq binders de la spine `A`, `B`, motif, mineur et témoin sont au régime zéro,
et le binder interne du motif est non nul. Les quatre annotations internes au
mineur restent arbitraires. La membership terminale du recursor, combinée à
ces six faits seulement, suffit à dériver que le `Iff` stocké force l'égalité.
Il s'agit d'une factorisation positive strictement plus locale, pas encore
d'une affirmation de minimalité.

Un premier séparateur **sémantique local** est compilé, sans nouvelle
déclaration calculatoire dans `Type`. Il interprète le télescope exact de
`Iff.rec` avec tous ses bits au régime zéro. Le point de preuve habite encore ce
télescope ; simultanément, une valeur de `Iff` à graphe constant relie réellement
`empty` et `unitSet`, qui restent distincts. La membership du recursor ne force
donc pas à elle seule l'égalité. Ce contre-modèle montre que l'`AnnotValid`
consommé par la factorisation positive n'est pas éliminable par la seule ligne
terminale de membership.

La comparaison aux producteurs historiques réels est désormais compilée. Le
noyau producteur a été affaibli jusqu'au run `inferTypeCore` du type stocké
épinglé. Ce même noyau est fourni indépendamment par le `MemberValRun` de la
voie modelée et par `checkNativeRec` dans la voie native. Dans les deux cas, il
reconstruit les cinq égalités de régime zéro et la non-nullité du binder interne
du motif. Le séparateur « tous les bits à zéro » est donc exclu des sorties des
deux producteurs opérationnels pertinents.

La capacité historique obtenue est pin-gardée : elle ne demande les six faits
que lorsqu'un lookup `Iff.rec` porte exactement le type effacé canonique. Cette
garde évite de contraindre une déclaration homonyme non standard. Sa stabilité
est prouvée séparément sur les membres non-recursors, le provisionnement et le
fold des règles, les projections, la voie inductive modelée, la voie native,
les déclarations `defn`, `thm`, `opaque`, `axiom`, les six blocs de base et le
dispatch `DeclRun` complet. Le fold `checkDeclsPure` la reconstruit ensuite
depuis `Env.empty` sans appeler `EnvModelM.type_wellDenotedV` ni les interfaces
globales `InferClaim` ou `DefEqClaim`.

Ainsi, pour le parcours pur accepté, les six faits sont une conséquence
reconstructible de l'histoire et ne justifient pas un champ de `B1`. La
membership terminale de `Iff.rec` et cette conséquence suffisent au consommateur
`propext`; l'ancienne prémisse locale `AnnotValid` disparaît entièrement de ce
raccord spécialisé. Il ne s'agit toujours pas d'une minimalité : aucun
séparateur ne montre que les six faits constituent la plus faible interface.
Le raccord au parcours cached exact de `FullyChecked` est maintenant compilé
dans `ScratchCachedBridge.lean`. L’usage de `EnvModelM` par le pont publié se
réduisait ici à sa projection `EnvWF`. Cette dernière est reconstruite
directement depuis les données syntaxiques des runs : les quatre déclarations
à une constante, les six blocs de base, la voie inductive modelée et la voie
inductive native sont toutes fermées séparément. Le walk de `InstallRun`
transporte ensuite le couple
`EnvWF × StoredIffRecBits`; les déclarations de valeur différées consomment
leurs vrais certificats `GroupChecked` à leur position de phase B. Le théorème
terminal donne donc :

```text
FullyChecked
→ EnvWF final
  ∧ StoredIffRecBits final
```

sans appel à `fullyChecked_sound`, sans construction de `EnvModelM` et sans
réintroduction de `InferClaim` ou `DefEqClaim` dans le carrier. Le scratch
compile avec Lean 4.33.0 ; son empreinte SHA-256 est
`E7794DE48615C5C7E20377F9CA9B4AEEEFF5ACE548BC50483870ECEF143A4C4E` et ses
audits rapportent uniquement `propext`, `Classical.choice` et `Quot.sound`,
hérités de ConLeche, sans `sorryAx`.

Le filtre d'atteignabilité a ensuite exclu exactement ce premier
contre-modèle. `ScratchChoiceReachability.lean` prouve qu'aucun
`MemberValRun .verified` ne peut produire le `Nonempty` effondré : le corps
`Sort 0` infère `Sort 1`, donc la validation impose `.never` au binder
extérieur, contradictoirement à `.ifAllZero []`. Cette exclusion est
indépendante du fuel, de l'environnement, du membre brut et des noms du bloc.
Le scratch compile sans `sorryAx`; son empreinte SHA-256 est
`8EC8E2B46AB7DFA016BC924D80AB6EDB477E60F4E275F2CC5378C6195EA9D631`.

Le test a alors été repris avec les métadonnées canoniques. Une sémantique
pathologique du former `Nonempty` et de son constructeur satisfait encore
séparément leurs lignes terminales, mais ne s'étend pas librement au recursor
canonique. `ScratchChoiceCanonicalClosure.lean` explique positivement cette
résistance : à type canonique du recursor, sa seule ligne terminale de
membership force déjà un témoin du type sous-jacent; la membership du
constructeur donne la direction inverse et reconstruit l'accord avec la double
négation. Ces deux conséquences ferment le résidu local de `choice` sans
`EnvModelM`, `InferClaim` ni interface globale d'`AnnotValid`. Ce contrôle exact
compile avec l'empreinte SHA-256
`5F0E0B1F12CB23EE6B7E29F3F4182680F65A15748B51C1B3339468F41E522EA0`.

Le weakening producteur/consommateur a ensuite montré que le type annoté
canonique complet de `Nonempty.rec` était encore une enveloppe trop forte.
`ScratchChoiceCanonicalProducer.lean` inverse le vrai `inferTypeCore`, puis les
frontières `MemberValRun` et `ConstantValRun`, et n'extrait que cinq régimes :
les quatre binders extérieurs consommés sont propositionnels et le domaine du
motive est strictement positif. Le binder interne au minor est délibérément
absent. Son empreinte SHA-256 est
`8FC99BF468C4173FBB04927C6A6E9C57B84D41C27A05AF060F08397FDECD01A6`.

`ScratchChoiceWeakenedClosure.lean` referme ensuite le consommateur depuis ces
cinq faits seulement. Le minor est construit séparément selon son régime
arbitraire : `pt` au régime propositionnel, une lambda au régime positif; son
domaine est vide sous l'hypothèse contradictoire, donc aucune propriété du
binder interne n'est requise. Les cinq bits suffisent à reconstruire
`StoredNonemptyForcesWitness`, `ChoiceDnegAgreement`, puis la membership de la
feuille `choice`. La capacité productrice provisoire
`StoredNonemptyChoiceSupport` est gardée par les pins exacts; l'exactitude du
constructeur est correctement indexée par la présence du même former épinglé,
au lieu d'être exigée isolément. Le scratch compile sans `sorryAx`, avec
l'empreinte SHA-256
`FA2948497EC975A77C275B41112837E541B76A5EB3794E1286373D54FA136B99` ; les
audits n'ajoutent que les axiomes hérités de ConLeche.

Ainsi le séparateur initial ne force pas encore une mémoire persistante : il a
révélé une donnée de constitution que le producteur vérifié exclut, puis cette
donnée a elle-même été affaiblie jusqu'aux cinq régimes effectivement consommés.
Le raccord ouvert est maintenant précis : construire et transporter le support
pin-guarded depuis les producteurs inductifs modelé et natif. Cette étape doit
préserver explicitement la relation historique former→constructeur; elle ne
doit ni revenir au type canonique complet du recursor, ni réintroduire le modèle
sémantique général.

Ce résultat ferme le pont cached pour la première relation locale du cas
`propext` : les bits historiques requis pour montrer que le `Iff` stocké force
l’égalité sont reconstructibles depuis `FullyChecked` et ne justifient donc
toujours aucun champ de `B1`. Il ne ferme pas encore la nouvelle feuille
terminale `propext`. Le premier résidu est désormais la seconde relation locale
de la factorisation positive : reconstruire, sans `EnvModelM.eq_law`, que le
`Eq` stocké à l’instance exacte `u := 1` se lit comme `eqv A B`. C’est cette
relation qu’il faut maintenant descendre vers ses producteurs réels, affaiblir
et séparer avant de rouvrir une autre branche.

Cette seconde relation a maintenant franchi les deux premiers tests dans
`ScratchPropextEqProducer.lean`. La preuve positive factorise la loi consommée
par `propext` à travers l’équation de la seule feuille `Eq` à l’instance
`u := 1`; `eqValAV_app₃` suffit ensuite à produire exactement `eqv A B`. Le
producteur de base a été reconstruit directement au niveau de la slice par
`TerminalSlice.consEq` : il installe la tour canonique `eqValAV` depuis
`TerminalSlice + fraîcheur + EnvWF`, sans construire `EnvModelM` ni appeler
`EqLaw`.

Le séparateur requis est également compilé. Une `TerminalSlice` contenant le
vrai `eqA`, dont la feuille est une relation toujours fausse, satisfait encore
la lecture et la membership du type stocké de `Eq`; elle réfute pourtant aussi
bien l’équation canonique de feuille que la loi occurrence-spécifique
`StoredEqValueAtPropext`. Ainsi :

```text
TerminalSlice + Eq bien typé
↛ Eq se lit comme eqv à l’occurrence propext
```

Ce résultat montre une insuffisance constructive réelle de `B0W`, et non un
échec de recherche de preuve. Il force une capacité sémantique historique sur
la réalisation choisie, mais ne justifie pas encore un champ de `B1` : il reste
à démontrer que la capacité occurrence-spécifique est produite puis conservée
par toutes les transitions réelles qui peuvent suivre l’installation de `Eq`.
L’équation complète de feuille reste une enveloppe productrice ; seule la loi
de valeur occurrence-spécifique est actuellement démontrée nécessaire au
consommateur. Le scratch compile avec Lean 4.33.0, sans `sorryAx`; son empreinte
SHA-256 est
`2D5B8D8CB3D20359531B36C2D99E4B0624721AE2FEAFE8BB51C0EE3E0B3EDCC6`, et les
audits rapportent seulement `propext`, `Classical.choice` et `Quot.sound`,
hérités de ConLeche. La conservation générique est également fermée : tout
`TerminalSlice.cons` à un nom distinct de `Eq` conserve
`StoredEqValueAtPropext` sans consommer aucune propriété sémantique de la
nouvelle feuille. La première spécialisation réelle est fermée : les branches
`defn`, `thm` et `opaque` reconstruisent chacune leur successeur exact depuis
leur support local, puis conservent la loi `Eq` par le seul fait que le checker
interdit à ces déclarations ordinaires d’utiliser le nom réservé `Eq`. Le garde
propositionnel propre à `thm` et le certificat optionnel de réduction propre à
`opaque` n’interviennent pas dans cette conservation. Aucune nouvelle prémisse
sémantique n’est requise.

La branche `axiom` est désormais décomposée sans hypothèse uniforme cachée.
Le constructeur générique qui installe une feuille d’axiome reconstruit la
slice exacte depuis `ConstantValRun` et les seuls faits sémantiques locaux de
la feuille ; la capacité `Eq` est ensuite préservée uniquement par la
réservation du nom. Le skip toléré conserve littéralement le témoin. La
sous-branche `Lean.trustCompiler` est entièrement fermée depuis la slice : son
pin identifie le type stocké à `True`, et la feuille stockée de `True.intro`
fournit déjà la membership requise. La sous-branche standard `propext` est
également fermée sans modèle riche : `StoredIffRecBits` et
`StoredEqValueAtPropext` produisent directement la membership de la nouvelle
feuille, qui conserve ensuite la loi `Eq`.

Les deux résidus axiomatiques restants sont exposés à leur bonne granularité.
Pour `choice`, toutes les obligations syntaxiques et la dépendance en niveau
sont reconstruites depuis le pin ; seul reste le jugement de membership de la
feuille canonique `choice` dans la lecture exacte de son type stocké. Pour
`ofReduceNat`/`ofReduceBool`, la feuille `.prf` et toutes ses obligations
structurelles sont immédiates ; seul reste son jugement de membership. Ces
jugements sont des obligations transitionnelles locales, pas des champs
proposés pour `B1`.

Le premier weakening du résidu `choice` est maintenant compilé. La preuve
positive réelle se factorise, après les lectures et le pinning déjà
reconstructibles, par deux relations seulement : l'accord entre la lecture du
`Nonempty` stocké et l'espace de double négation attendu
(`ChoiceDnegAgreement`), puis le fait que toute valeur appartenant à cette
lecture stockée force effectivement un témoin du type sous-jacent
(`StoredNonemptyForcesWitness`). Ces relations suffisent au jugement local de
membership de la feuille `choice`, mais ne sont pas revendiquées minimales.

`ScratchChoiceSeparator.lean` construit une `TerminalSlice` complète dont les
types stockés sont lus exactement et dont toutes les lignes de membership sont
habitées, tout en interprétant la famille `Nonempty` de façon effondrée. Sur
cette réalisation, les deux relations locales sont réfutées constructivement à
`A := SetTheory.empty`. Le même scratch ferme en outre, sans `native_decide`,
le `ConstantValRun` du type canonique de `choice`, le garde
`stdAxiomOk = true`, puis un véritable `DeclAxiomRun .verified` installant
`choice`. Avec la fermeture eta, il fournit donc un témoin `B0W` concret et une
transition `choice` réellement acceptée sur lesquels les deux relations locales
restent impossibles. Il s'agit d'une non-reconstruction universelle depuis
`B0W + transition`, et non d'un simple échec de recherche de preuve.

Ce séparateur ne franchit pas encore le filtre d'atteignabilité. Les métadonnées
de binders de la famille `Nonempty` effondrée diffèrent de celles des sorties
canoniques `nonemptyA` et `nonemptyRecA`; le checker de l'axiome `choice` ne
revalide pas cette histoire antérieure. Il n'est donc pas encore établi qu'un
préfixe produit depuis `Env.empty` puisse porter ce témoin. Le scratch compile
avec Lean 4.33.0 ; son empreinte SHA-256 est
`B0807BC1F1C800E1AD2B310B17EF26C1D06012F542D94250E0BA051BAB3289AA`, et ses
audits rapportent uniquement `propext`, `Classical.choice` et `Quot.sound`,
hérités de ConLeche, sans `sorryAx`.

La frontière `choice` est désormais fermée au niveau historique recherché.
`ScratchChoiceSupportTransport.lean` transporte
`StoredNonemptyChoiceSupport` et l'auxiliaire d'ordre
`PinnedIntroResolvesFormer` à travers les deux voies inductives réelles
(modelée et native), les constructeurs, recursors et projections, les six
blocs de base, les quatre déclarations ordinaires et le dispatch `DeclRun`
complet. Le fold pur les reconstruit depuis `Env.empty` sans `EnvModelM`.
Son empreinte SHA-256 est
`B07628460CFED68E27968ADF6D193050475BF3717F69184E30D1DAC01C680F31`.
Le pont cached a été généralisé seulement après apparition de cette seconde
propriété indépendante; `ScratchCachedBridge.lean`, d'empreinte
`161D6281FE8547396628E65800C22EBE0113172CB24A794B39B81F3E6A9A1B64`,
reconstruit donc la propriété finale depuis le vrai `InstallRun`.
`ScratchChoiceCachedClosure.lean`, d'empreinte
`B27129ACA537AB44FD5822679C09E79BFBE5B45ABD5F32E6AA2B1DA31C371A3B`,
compose ce résultat avec le consommateur affaibli : `FullyChecked` fournit le
support historique exact, puis la vraie installation de `choice` étend la
slice sans `fullyChecked_sound`, `EnvModelM`, `InferClaim` ni `DefEqClaim`.

L'analyse indépendante de `ofReduceNat`/`ofReduceBool` est ouverte dans
`ScratchOfReduceClosure.lean`. La membership de `.prf` se factorise exactement
par deux relations locales : la valeur de `Eq.{1}` sur tout type élément
appartenant à `univ 1`, et l'identité de l'opération de réduction sur les
éléments de son type. La seconde occurrence force un renforcement réel de
l'ancienne capacité `Eq` limitée au cas `propext`; la nouvelle interface
`StoredEqValueAtUniverseOne` se projette encore vers celle de `propext`, est
produite par le cons canonique de `Eq`, et se transporte à travers tout cons
frais de nom distinct. Une adaptation du séparateur `falseEqSlice` prouve
constructivement que la terminal slice ne détermine pas cette interface plus
forte. Le scratch compile sans `sorryAx`; son empreinte SHA-256 est
`E30B4832425E2C4ABED24D5D799F9EBEF122CA3103D9C15765A5F3281EAAC906`.

Le producteur réel de l'identité a ensuite été coupé à sa première dépendance
sémantique dans `ScratchReduceIdentityProducer.lean`. Le `ReducePinRun`
contient un succès opérationnel précis de `isDefEqCore`; une seule instance
de `DefEqClaim` transforme ce certificat en égalité sémantique locale, sans
reconstruire `ReduceOps`. Sous la closedness déjà disponible pour la feuille,
cette égalité du certificat est démontrée équivalente à l'identité de
l'opération sur son type d'éléments. Le weakening occurrence-spécifique a donc
atteint son plancher : cette égalité n'est pas une capacité intermédiaire plus
faible à persister, mais une présentation structurée du jugement consommé.
Le scratch compile sans `sorryAx`; son empreinte SHA-256 est
`3B7F90C3CA8EB3E455A27084D9C5FD8D6EADAAB11BC8B4CA550339378ADD994B`.

Le séparateur demandé est désormais construit dans
`ScratchReduceIdentitySeparator.lean`. Il fournit un vrai `ReducePinRun` pour
`Lean.reduceNat`, un témoin `B0W` avant et un témoin `B0W` après. La réalisation
successeur attribue toutefois à l'opération la valeur sémantique bien typée de
`Nat.succ`; l'identité requise est alors réfutée constructivement sur `0`.
Ainsi, l'existence état par état d'une slice terminale ne détermine pas la
compatibilité historique exigée par le futur consommateur `ofReduceNat`.

Le filtre de productibilité est traité séparément dans le même scratch. Le
théorème `noEnvModelM_has_badSuccessorAssignment` montre qu'aucun `EnvModelM`
sur le même environnement ne peut posséder l'affectation sémantique du mauvais
successeur : le champ producteur réel `ReduceOps` force l'identité et exclut ce
contre-modèle. Ce second résultat ne rétracte donc pas le séparateur sur `B0W`;
il localise exactement l'information que la constitution riche ajoute et que
l'ombre terminale oublie. Le scratch compile sans `sorryAx`; son empreinte
SHA-256 est
`DAF96A202BB3E91D9EACE9ACAB2FF223DBB8DC02056A9CAAB260B127076560E5`.

Ce premier séparateur état-par-état a depuis été renforcé. Dans
`ScratchReduceIdentityLocalSeparator.lean`, le même témoin sémantique ancien
est conservé et un vrai `ReducePinRun` est construit ; l'obligation exacte
`ReduceCertificateSemanticTransport` est alors réfutée directement, sans
choisir de témoin successeur. Son empreinte SHA-256 est
`7FBA2A1301AA53AFA9C7EBC976C7DB50589B49AAF75ABA233DE4562EF9BBFBD2`.

Le filtre d'atteignabilité syntaxique est également franchi dans
`ScratchReduceIdentityReachableSeparator.lean`. Le préfixe réel
`basis Nat ; defn alias` est accepté depuis `Env.empty`, puis la transition
`ReducePinRun` est exécutée sur l'environnement obtenu. Une réalisation `B0W`
affaiblie de cet environnement atteint peut encore attribuer `Nat.succ` à
l'alias et réfuter le transport du certificat. Il s'agit d'une atteignabilité
de l'environnement syntaxique, non de l'affirmation que cette mauvaise
réalisation est la sortie riche du fold. Le scratch, d'empreinte
`14DB9A4BC675DDDCC9FCDB87D6CBC4C4D77DC4579DDC0540B2EFEF4BBBE8BDA5`,
compile sans `sorryAx`.

`ScratchReduceIdentitySupport.lean` a ensuite testé le premier enrichissement
facile. La propriété `StoredReduceIdentity`, obtenue en retirant de `ReduceOps`
le conjunct de stockage du type élément, est constructivement équivalente à
`ReduceOps` sur un `EnvModel` : le conjunct retiré se reconstruit déjà depuis
les pins et `EnvWF`. Surtout, l'ajout de toutes les identités des opérations
déjà stockées ne ferme pas la nouvelle installation : le certificat peut
déplier une autre définition ancienne, ici l'alias. Le séparateur atteignable
survit à cet ajout. Le scratch a pour empreinte
`9BD837D6D2BB2B2D10CFAC39B361E2B54E843841C66E1354C1FD1812CE5C3698`.

La première factorisation positive de ce résidu est maintenant compilée dans
`ScratchReduceIdentityFromDelta.lean`. Le producteur δ affaibli
`AcvalDefnReadableSeed` fournit une projection encore plus petite,
`AcvalDefnReadableAppAgreement`, qui oublie entièrement l'observation de
membership et ne conserve que l'accord applicatif sur les arguments réellement
lus. Au niveau local des deux lectures, un séparateur non vacue montre que cet
accord applicatif n'implique pas la seed complète : les applications peuvent
coïncider alors que sa loi d'observation de membership échoue. Cette stricte
séparation locale ne vaut pas encore théorème de stricte faiblesse entre les
deux providers globaux. Pour l'alias atteint et l'unique variable du certificat, cette relation
donne l'accord entre l'application de la tête stockée et celle du corps lambda ;
la loi sémantique de la lambda identité produit alors exactement
`ReduceCertificateSemanticTransport`. Ni `DefEqClaim` ni `EnvModelM` complet
n'apparaissent dans cette preuve. Le même contre-modèle réfute cette projection,
donc la nouvelle interface n'est pas cachée dans `B0W`. Ce raccord prouve une
réutilisation transversale réelle de la capacité historique δ ; il ne prouve
pas encore qu'elle traite tout `ReducePinRun`. Son empreinte SHA-256 est
`749C8D00D40AC0A6316A5AE0514E13651338B3F6443E767928A0F608CC792B0C`.

Le premier test indépendant β est fermé dans
`ScratchReduceIdentityFromBeta.lean`. Une valeur réelle, constituée par
l'application de la lambda identité sur le type `Nat → Nat` à la lambda
identité sur `Nat`, satisfait le vrai `ReducePinRun`. Sa lecture annotée est
reconstruite depuis le run et les pins déjà présents ; deux applications de la
loi sémantique positive des lambdas donnent ensuite exactement
`ReduceCertificateSemanticTransport`. Ainsi cette occurrence β n'exige aucune
capacité historique supplémentaire au-delà de `B0W`, contrairement à
l'occurrence δ précédente. Cette asymétrie est un résultat sur les producteurs,
pas encore une couverture de toutes les exécutions possibles de
`isDefEqCore`. Le scratch compile sans `sorryAx`, a pour empreinte SHA-256
`0563B9E912C1A3E8DE89CA1D7D7C6C37A524CF7EDDD7BA1E1DE3BB8DFA7B3769`,
et ses audits ne rapportent que les trois axiomes hérités de ConLeche.

Le troisième producteur imposé par le même résidu est maintenant fermé dans
`ScratchReduceIdentityFromIota.lean`. Le préfixe réel des bases `PUnit` puis
`Nat` est accepté et le fold riche fournit séparément l'existence d'un
`WalkWitness` à cet état productible ; une occurrence exacte de `PUnit.rec`
sélectionne la lambda identité sur `Nat`, et son certificat est vérifié par le vrai
`isDefEqCore`. La dissection conserve deux lectures distinctes : celle du RHS
sélectionné et celle de la valeur source stockée par `ReducePinRun`. La preuve
finale porte bien sur cette dernière, de lecture
`punitRec [0, 1] motive identity PUnit.unit`. Les pins de la base, la loi
`punitRecV_app` et l'appartenance du certificat à `Nat` reconstruisent alors
directement `ReduceCertificateSemanticTransport`. Ainsi, comme β, cette
occurrence ι concrète se ferme depuis `B0W` sans champ persistant nouveau ; elle
ne constitue pas encore le `DeclOpaqueRun` complet qui enveloppe cette
sous-transition et ne généralise pas encore le résultat à tout `ReducePinRun`.
Le scratch compile
sans `sorryAx`, a pour empreinte SHA-256
`35425F793B19B560537AD917607F0B278EBF6B26F463548EA8935D5F199B8ED0`, et
ses audits ne rapportent que les trois axiomes hérités de ConLeche.

Le premier raccord à la déclaration complète est maintenant compilé dans
`ScratchReduceOpaqueBridge.lean`, sur l'alias-δ atteint. La preuve construit
séparément `ConstantValRun` pour le type brut de `Lean.reduceNat`,
`ValueFrontRun` pour la valeur alias, puis `DeclOpaqueRun` et le vrai `DeclRun`.
Elle ne confond pas ce paquet avec `ReducePinRun` : le checker vérifie aussi
`isDefEqCore` entre la valeur annotée et le pin annoté, obligation que la
projection `ReducePinRun` n'enregistre pas. Le lemme local
`checkReducePin_of_run_and_pinEq` recompose le contrôle opérationnel depuis
le run et cette égalité supplémentaire ; la même occurrence δ la reconstruit
par dépliage. Les deux moitiés de `checkDecl` sont ensuite prouvées, puis
`checkDeclsPure` accepte le préfixe complet depuis `Env.empty`. Enfin,
`reachableAcceptedSeparator` raccorde ce préfixe accepté au contre-modèle
`B0W` antérieur, qui réfute encore le transport sémantique du certificat.
La réalisation affaiblie n'est toujours pas présentée comme le témoin du fold
riche. Ce résultat ne prouve ni que l'égalité au pin est indépendante de
`ReducePinRun` en général, ni le raccord β/ι, ni le cas générique.
Le scratch externe, compilé contre le commit ConLeche épinglé avec Lean
`v4.33.0`, a pour empreinte SHA-256
`F44D4419EB9ED4749C67E080A479790FDEBF99B3EA6CB7036EFF84188AFFA4F4` ;
ses audits ne rapportent que les trois axiomes hérités de ConLeche, sans
`sorryAx`.

Les deux autres occurrences de reduce ont maintenant leur raccord
**indépendant au pas opaque complet**. `ScratchReduceOpaqueBeta.lean` prouve
séparément l'inférence de la tête et de l'argument, la vérification ordinaire
de la valeur, l'égalité au pin, `DeclOpaqueRun`, `DeclRun`, `checkDecl` et
`checkDeclsPure` depuis le préfixe accepté. Le certificat sémantique β était
déjà reconstruit localement depuis `B0W` dans
`ScratchReduceIdentityFromBeta.lean` : ce raccord n'ajoute aucun champ au
carrier. Le nouveau scratch β n'importe pas le bridge opaque δ. Son SHA-256
est `5F65AEE69247186C3CD35C5BE94A6C7D6F09F70B9E6E9C76B0A94F1826F293D5`.

`ScratchReduceOpaqueIota.lean` ferme les mêmes obligations opérationnelles
pour la valeur identité issue du vrai run ι `.plain`, sur le préfixe accepté
`PUnit` puis `Nat`. Le type effectivement inféré n'est **pas** le type déclaré
en tant qu'expression : c'est l'application de la lambda-motif à `PUnit.unit`.
La preuve construit ce résultat exact au carburant `7`, le relève à `50` par
monotonie, puis prouve séparément l'égalité définitionnelle avec le type
déclaré. Elle prouve également l'égalité au pin, qui n'est pas incluse dans
`ReducePinRun`. Les contrôles calculés sont prouvés par `decide` avec
dépliage intégral sous vérification du noyau, et non inférés d'un `#eval`.
Le SHA-256 du scratch ι est
`985045FA0A431B58C86406AB70179E96AFF4CD9E50EE165ED55C3A14ED7618B0`.
Les deux fichiers sont hors du dépôt, compilent sans avertissement ni
`sorryAx` avec Lean `v4.33.0` contre le commit ConLeche épinglé ;
`#print axioms` n'affiche que `propext`, `Classical.choice` et `Quot.sound`
hérités du développement externe. Aucun des trois cas δ/β/ι n'établit
encore la reconstruction uniforme pour tout `ReducePinRun`, ni la
conservation inductive de cette capacité dans le fold riche ou affaibli.
Les théorèmes `reachableBetaCertificateExists` et
`reachableIotaCertificateExists` composent, pour chacun de ces deux préfixes
réellement acceptés, l'existence d'un témoin ancien fourni par le fold riche
avec la reconstruction locale du certificat depuis sa slice affaiblie.
Ils ne prétendent pas que le témoin sémantique nouveau est obtenu par un fold
sur `B0W`.

L'ouverture du **producteur générique** a maintenant franchi sa première
frontière. `ScratchReduceGenericFront.lean` prouve depuis `EnvModel` et les
seuls `ValueFrontRun` / `ConstantValRun` les lectures annotées de la valeur et
du type pour chaque `ψ`. La lecture de la valeur est choisie sans ambiguïté
par `getD` après succès de `denoteMeta` ; sa closedness et sa dépendance
exclusive aux paramètres de niveaux déclarés suivent de `base2` et des
gardes syntaxiques du run. `certificateUsesFrontValue` aligne par déterminisme
le `value'` choisi dans le front run avec celui du `ReducePinRun` ; aucun
`EnvModelM`, `InferClaim` ni `DefEqClaim` n'est requis à cet étage. Le fichier
externe compile avec Lean `v4.33.0` contre ConLeche épinglé ; son SHA-256 est
`6DA87642D596D3E705BFE106FA7F7BADB38F560EF314A4CE7A85A50BB7EB507D`.
Les audits n'indiquent que les trois axiomes hérités de ConLeche, sans
`sorryAx`. Le même fichier ferme en outre `hAok` lorsque la valeur acceptée
est une constante : `readConstantWellDenoted` et
`valueFrontConstantWellDenoted` reconstruisent sa bonne dénotation depuis
`base2` et la lecture réussie du `ValueFrontRun`. Cela ne traite pas encore
`hAok` pour une valeur composée arbitraire. Pour la même sous-classe constante,
`valueFrontConstantAnnotValid` factorise positivement `hAvalid` par la
validité de **la seule ancienne feuille lue**, aux niveaux effectivement
substitués ; ce n'est pas une reconstruction de cette validité depuis `base2`
ni une décision de la persister. Pour une valeur constante, la prémisse et la
conclusion sont reliées par la lecture exacte de cette feuille : cette
factorisation identifie la provenance immédiate de la ligne, **sans** prouver
qu'une capacité intermédiaire strictement plus faible a été trouvée.

La preuve réelle `reduceOps_install` (`ConLeche/Model/ReduceOps.lean`)
consomme ensuite `hAok`, `hAvalid`, `hmemA`, le `WellDenotedV` du type
déclaré, puis le grade `WellDenotedV` de l'application au certificat avant
l'appel à `DefEqClaim`. Il serait méthodologiquement
incorrect de désigner immédiatement ce dernier comme l'unique résidu
générique. `ScratchReduceOpaqueProducerRows.lean` teste ces lignes sur le
**séparateur δ atteint**, et établit dans un même théorème que la déclaration
opaque complète est acceptée, que la nouvelle valeur annotée est bien
dénotée, valide et appartient au type déclaré, que le type déclaré est
`WellDenotedV`, et que l'application du certificat est `WellDenotedV` sous
le `Sat` réel du contexte élément ; pourtant le transport sémantique du
certificat reduce est faux pour la réalisation `B0W` choisie.
Le type déclaré est lu sur le même `ψ` que la valeur. Ce résultat situe la
rupture de **cette occurrence** après ces lignes et le grade applicatif,
sans établir leur reconstruction uniforme depuis `B0W + DeclOpaqueRun` pour toute
installation reduce. Le scratch externe compile sous le même environnement ;
son SHA-256 est
`2F0C200C9DC254EEBA284A2F7261B8D0E02C84296FAF6805E9A4A6724D2410B6`.
Ses audits ont le même statut d'axiomes hérités, sans `sorryAx`.

Le test de l'instance exacte de `DefEqClaim` est maintenant compilé dans
`ScratchReduceOpaqueDefEqInstance.lean`. Sur ce même témoin affaibli et le
même certificat reduce, la preuve fournit le `isDefEqCore` réussi, le
scoping, les bornes et les feuilles des deux termes, leurs `CtxOk` sur le
contexte élément réel, leurs lectures à profondeur `1` et leurs
`WellDenotedV` sous `Sat`. Elle réfute néanmoins **l'instance précise**
`DefEqClaim .verified bad.slice.base2 (fun _ => 0) 50`, puis la famille
`∀ ψ, DefEqClaim ... ψ 50`, et raccorde cette réfutation au préfixe et au
`DeclRun` complets acceptés. Ce n'est pas une réfutation du `DefEqClaim` de
la réalisation riche produite par le fold : celle-ci ne peut pas être le
témoin affaibli choisi. Ce séparateur isole l'échec de la conversion
sémantique d'un verdict defeq sur une occurrence, sans encore montrer
quelle donnée historique la rétablit le plus faiblement ni sa conservation
sur toutes les transitions. Le fichier externe compile sous Lean `v4.33.0`
contre le commit ConLeche épinglé, SHA-256
`BD00D0E22E358305E2CC79BD1502DF400E5AAD1E17A22D23D287A994EE68694E` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Un séparateur **indépendant**, situé plus tôt dans l'ordre des lignes du
producteur, est compilé dans `ScratchReduceOpaqueValidRowSeparator.lean`.
Sur le même environnement syntaxique atteint par le préfixe accepté et le
même `DeclOpaqueRun` δ complet, il construit une autre réalisation
`TerminalSlice` : la lecture de la valeur est une lambda dont le corps est
une égalité sémantiquement fausse. Cette valeur est `WellDenotedV` et
appartient au type déclaré `Nat → Nat` pour toutes les valuations `ψ, ρ`,
mais elle n'est `AnnotValid` pour aucune `ψ, ρ`, car son sous-terme `badBit`
viole le grade requis. Le théorème
`reachableAcceptedWithInvalidValueAnnotation` conserve dans un seul témoin
le préfixe `checkDeclsPure` accepté, le vrai `DeclRun`, les lectures exactes,
la bonne dénotation, la membership et la réfutation de `hAvalid`. Il sépare
donc constructivement la reconstruction universelle de `hAvalid` depuis
`B0W + DeclOpaqueRun`, même dans le sous-cas où `hAok` et `hmemA` sont vrais.
La syntaxe et le pas sont atteignables ; la réalisation affaiblie choisie
n'est pas celle produite par le fold riche. Ce résultat n'établit ni que
`hAvalid` est l'unique résidu générique, ni qu'il doit être persisté tel quel.
`reachableAcceptedWithoutOldLeafValidity` raccorde en outre ce même
contre-modèle à la **prémisse exacte** du théorème positif
`valueFrontConstantAnnotValid` : la validité de la feuille ancienne aux
substitutions de niveaux du run ne se reconstruit pas sur cette occurrence.
Le scratch externe compile sous Lean `v4.33.0` contre le commit épinglé,
SHA-256
`4B01403900AF5A9FA8CAE39DDDADA08428EF9D12EE89CD3806E0B4FA07ED356E` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Le premier test composé de `hAok` est positif dans
`ScratchReduceOpaqueBetaWellDenoted.lean`. La lecture exacte à profondeur
zéro de la valeur β est reconstruite depuis n'importe quelle ancienne
`TerminalSlice` sur le préfixe accepté. Les deux lambdas annotées sont
`WellDenotedV`; pour leur application, un seul cadre partagé est construit :
la tête appartient au `piR` du type fonctionnel, et l'argument appartient au
*même* domaine. `AnnotValid` est également reconstruit structurellement :
le seul `Pi` du terme a un niveau de codomaine positif.
`reachableBetaAcceptedFirstRows` raccorde les deux lignes au même
`checkDeclsPure` et au vrai `DeclRun` opaque, pour tout ancien
`WalkWitness`. `reachableBetaAcceptedProducerRows` ajoute, pour les mêmes
`ψ` et `ρ`, l'appartenance de la valeur au type déclaré effectivement lu et
la bonne dénotation de ce type. `betaCertificateApplicationWellDenoted`
ferme aussi le grade de l'application au certificat sous le `Sat` du contexte
élément réel ; il utilise la membership du même représentant de `Nat` issue
de la slice ancienne. Seul le passage `isDefEqCore →` égalité sémantique reste
à traiter pour cette occurrence, bien que son certificat local ait déjà été
reconstruit séparément. Aucun `InferClaim`, `EnvModelM` ou fait sémantique ajouté au
carrier n'est consommé. C'est la fermeture de ces quatre lignes sur
**cette occurrence β**,
pas une preuve uniforme pour toutes les valeurs composées ; ι et les autres
formes restent à tester avant d'annoncer le statut générique. Le scratch
externe compile sous Lean `v4.33.0` contre le commit épinglé, SHA-256
`F0EFD03C89DAAF640DCC03C51FC249DD0EFF9A0DBAD1E73C107A51F598FD0BEC` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Le test ι composé est également positif, mais par une construction
**indépendante de la preuve β** dans
`ScratchReduceOpaqueIotaWellDenoted.lean`. Pour la source annotée exacte
`PUnit.rec` appliquée à son motif, son minorant et `PUnit.unit`, la preuve
construit successivement trois cadres `piR` compatibles avec ces trois
arguments. Le motif appartient à `punitMotiveSpace`, le minorant à sa fibre
au point `pt`, et `pt` à `unitSet`. Cela donne `WellDenotedV` du terme
composé sans `InferClaim` ; sa validité d'annotation est structurelle. La loi
`punitRecV_app` ramène sa valeur sémantique au minorant et donne son
appartenance au type fonctionnel déclaré, lu sur le même `ψ`. Le `Sat` réel
du contexte élément suffit enfin à la bonne dénotation de l'application au
certificat. `reachableIotaAcceptedProducerRows` regroupe les quatre lignes
pré-certificat et ce grade avec le vrai `DeclRun` et le préfixe
`checkDeclsPure` accepté, pour **tout** ancien `WalkWitness` de cet état.
Le fichier externe compile sous Lean `v4.33.0` contre le commit épinglé,
SHA-256
`09591731CEFBFE22130C0E668E0E0F0F6E40574F39563BAB972E786162E82CBE` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.
Ces deux occurrences composées positives ne prouvent ni un théorème uniforme
pour tout `ReducePinRun`, ni que δ est l'unique famille susceptible de
porter un résidu de validité.

Le premier producteur affaibli de la ligne δ `hAvalid` est testé dans
`ScratchReduceOpaqueDeltaBitAgree.lean`, sans créer de `B1`.
`deltaBodyReadAtZero` lit le corps de l'alias stocké depuis la seule base
faible. La relation existante `AnnotTerm.BitAgree` entre l'ancienne feuille
et cette lecture suffit alors à transporter `AnnotValid` au terme nouveau
effectivement lu. Le producteur riche `AcvalDefnInst` fournit cette relation
sur l'alias atteint, mais le témoin `B0W` du séparateur δ la réfute. Une paire
explicite de lambdas aux grades positifs `1` et `2` montre que `BitAgree`
n'impose pas l'égalité syntaxique des lectures. Cette stricte distinction est
établie **au niveau de la relation sur les lectures**, pas encore dans la
sous-classe des réalisations productibles du fold. `BitAgree` est donc une
interface productrice suffisante et non reconstructible depuis ce témoin
faible, mais ni sa nécessité minimale, ni sa persistance, ni sa stabilité sur
toutes les déclarations ne sont établies. Le scratch externe compile sous
Lean `v4.33.0` contre le commit épinglé, SHA-256
`C9490E5C6A874CF1EBB8334A2B9D75C9463294C4FE3AEB9C56A7BB42F7ED3B1C` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.
Le weakening possède aussi un **séparateur inverse sur le même préfixe
syntaxiquement atteint** : `reachableValidWithoutBitAgree` conserve
`checkDeclsPure` accepté et le vrai `DeclRun`, mais attribue `Nat.succ` à
l'alias dans un autre `B0W`. Sa valeur est `AnnotValid` pour toutes les
valuations, tandis que `BitAgree` avec la lecture du corps lambda est
impossible par forme de constructeur. Donc `hAvalid` seul ne force pas
`BitAgree` sur cet état atteint. La réalisation faible choisie n'est pas
celle du fold riche. Le test conjoint plus fort suit ci-dessous.

Le test conjoint demandé est maintenant compilé dans
`ScratchReduceOpaqueDeltaNonBitAgree.lean`. Une autre `TerminalSlice` du
**même préfixe syntaxiquement atteint** lit l'alias comme un β-redex annoté
qui dénote l'identité stockée. Pour ce témoin faible, le même préfixe est
accepté et le même vrai `DeclRun` opaque δ existe ; la valeur nouvelle est
`WellDenoted`, `AnnotValid`, membre du type déclaré exactement lu, et
l'application au certificat est `WellDenotedV` sous le `Sat` réel.
`ReduceCertificateSemanticTransport` est également démontré sur la lecture
de cet alias, mais `BitAgree` avec le corps stocké est impossible par forme
de constructeur (`app` contre `lam`). Le séparateur ne se borne donc plus
au converse depuis `hAvalid` seul : même la conjonction des lignes positives
et du transport de certificat ne force pas `BitAgree` dans la classe des
réalisations `B0W` sur cette occurrence acceptée. Plus fortement,
`betaAliasDeltaSuccessorSlice` construit la slice terminale suivante avec
égalité des lectures de l'ancien alias, et
`reachableWeakDeltaSuccessorWithoutBitAgree` y ajoute la composante eta pour
obtenir un véritable `WalkWitness` successeur du même `DeclRun`. Cette
préservation est **relative à cette occurrence et à ce témoin**, non une loi
universelle `Stable B0W` ; `betaAliasNotDefnInst` prouve même que cette
réalisation ne satisfait pas le producteur riche `AcvalDefnInst`. Cela ne
réfute pas la suffisance productrice de `BitAgree` pour `hAvalid`.
Le fichier externe compile
sous Lean `v4.33.0` contre le commit épinglé, SHA-256
`CD969EF86AC418FE06362641CB6CF1EEB2C6FC3CEADCAB9E7139A39CDD78BC6B` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Un séparateur **inverse** a été construit indépendamment dans
`ScratchReduceOpaqueDeltaGradeIndependence.lean`. L'alias d'une
`TerminalSlice` du même environnement atteint reçoit une application dont
la tête est une lambda constante renvoyant l'identité stockée ; son argument
est `eqE badBit badBit`. Cet argument appartient sémantiquement à `U₀`, mais
`badBit` porte un grade `Pi 0 0` invalide. La valeur entière est donc
`WellDenoted`, appartient au type `Nat → Nat` et a exactement
l'interprétation de la lambda identité, tandis que `AnnotValid` est faux.
Le théorème `reachableCertificateWithoutValueAnnotValid` raccorde ce témoin
au même préfixe accepté et au vrai `DeclRun` δ, prouve le transport du
certificat reduce depuis la slice ainsi construite et réfute la validité
d'annotation de la valeur nouvelle. En regard du témoin `Nat.succ`
(`AnnotValid` vrai, transport faux), cela sépare **dans les deux sens** les
capacités de validité d'annotation et de transport sémantique du certificat,
relativement aux réalisations faibles `B0W` sur une syntaxe atteinte.
`gradeAliasNotDefnInst` démontre explicitement que ce second témoin n'est
pas non plus productible par le producteur riche `AcvalDefnInst`. Ce ne sont
donc pas des séparateurs dans la sous-classe des réalisations productibles
par le fold riche ; aucune persistance n'en découle à elle
seule. Le scratch externe compile sous Lean `v4.33.0` contre le commit
épinglé, SHA-256
`74145567431C78B7A9DE0FCF1E451415861B078B562983DF05F53163FA7393E4` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Le premier retour au **producteur reduce générique** est positif pour la
ligne du type déclaré de `reduceNat`. Dans `ScratchReduceNatTypeRows.lean`,
`natStored_of_reducePinRun` extrait du vrai certificat opérationnel
`ReducePinRun` la présence exacte de la base `Nat` épinglée. Pour **tout**
ancien environnement satisfaisant cette prémisse et toute `TerminalSlice`
sur lui, `reduceNatTypeRead` identifie la lecture du type épinglé
`reduceNatCvA.type` à `Nat → Nat`, et `reduceNatPinTypeRow` prouve
`WellDenotedV` de cette lecture pour tous `ψ, ρ`. La ligne `hTaOk` ne
requiert donc aucun enrichissement historique pour `reduceNat`, même hors
des trois exemples concrets. Ce théorème ne couvre pas `reduceBool` : son
élément `Bool` n'est pas simplement le pin structurel de `Nat`, et sa
validité d'annotation reste à tester depuis la base faible. Le scratch
externe compile sous Lean `v4.33.0` contre le commit épinglé, SHA-256
`B463B06BCD4A6EFCEE7862380F4AC96DFA7E48579C9379177348C6206BEA6821` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Le test `reduceBool` a maintenant une **factorisation exacte** dans
`ScratchReduceBoolTypeRows.lean`. Le vrai `ReducePinRun` fournit un `Bool`
stocké avec `levelParams = []`; `reduceBoolTypeRead` identifie la lecture du
type déclaré à `Π Bool Bool`, avec la **même feuille Bool** dans le domaine
et le codomaine. Le théorème
`reduceBoolPinTypeRow_iff_oldBoolValid` établit, pour toute
`TerminalSlice` faible et toutes les valuations, l'équivalence entre la
ligne `hTaOk` (`WellDenotedV` du type déclaré) et `AnnotValid` de l'ancienne
feuille Bool. La moitié `WellDenoted` est déjà reconstruite depuis `base2` ;
le résidu exact de cette ligne est donc la validité d'annotation, pas une
théorie générale des types ou de l'inférence. Le scratch
externe compile sous Lean `v4.33.0` contre le commit épinglé, SHA-256
`74D2AE25D3410006877BF055806E7F6A4ADF4BFCA7B63DFF06AAE9384F32AF32` ;
ses audits ne signalent que les trois axiomes hérités, sans `sorryAx`.

Un séparateur **constructif et opérationnellement raccordé** est désormais
compilé dans `ScratchReduceBoolValidSeparator.lean` (SHA-256
`5997871A0C3DF3706B4C70E84F05EA8FDFA35EDACAF7275729DCBD5B0167D285`).
L'ancien environnement contient un `Bool` stocké à la forme exigée par le
pin ; `boolBadSliceWitnessExists` lui donne une vraie `TerminalSlice` dont
la feuille `Bool` est bien dénotée et appartient à son type stocké, mais
viole `AnnotValid`. `boolWeakEtaClosed` complète le témoin `B0W`.
`boolReduceRun`, `boolOpaqueRun`, `boolDeclRun` et `boolOpaqueAccepted`
établissent séparément le certificat reduce, la transition de déclaration
et l'acceptation par le checker de l'opaque `reduceBool` depuis **cet**
environnement. `boolAcceptedTypeRowSeparator` réfute alors la reconstruction
universelle de `hTaOk` depuis `B0W +` cette transition acceptée, par
l'équivalence exacte précédente. Le weakening du **consommateur effectif**
évite toutefois de compter cette ligne comme une seconde mémoire : sur
la valeur épinglée exacte, `reduceBoolPinnedValueRead` et
`reduceBoolValueGrade_iff_oldBoolValid` montrent que `hAvalid` de l'identité
est lui aussi équivalent à cette même validité de l'ancienne feuille.
`reduceBoolTypeRow_of_valueGrade` reconstruit donc `hTaOk` depuis `hAvalid`
sur cette occurrence, tandis que `boolAcceptedValueGradeSeparator` réfute
constructivement **la ligne `hAvalid` elle-même** sur la même déclaration
acceptée. Le résidu local est une seule détermination partagée entre deux
lignes, non deux champs historiques indépendants. Cette équivalence n'est
pas démontrée pour toute valeur arbitraire définitionnellement égale au pin.
`piOneApplicationWellDenotedV` ferme en outre le sous-but de grade de
l'application du certificat sous la forme épinglée `Π` de niveau `1`, sans
consommer `hTaOk` : sa condition de niveau `0` est impossible. Cela affaiblit
ce sous-but exact, **pas** le théorème générique `reduceOps_install`, qui
autorise un metadata de binder plus général.
Tous les audits de ce scratch ne signalent que les trois axiomes hérités de
ConLeche, sans `sorryAx`.

La portée reste délibérément bornée : aucune preuve ne montre que
`boolWeakEnv` est produit par `checkDeclsPure` depuis `Env.empty`, ni que sa
réalisation faible provient du fold riche. Le résultat force une capacité
supplémentaire pour la **reconstruction locale universelle** de la ligne
`reduceBool`, pas encore sa persistance dans un `B1` historique ; le
séparateur ne réfute pas à lui seul la stabilité faible de `B0W`. L'essai
diagnostique d'installation d'un bloc singleton `Bool` n'a pas fourni un
préfixe accepté ; cette observation n'est pas employée comme théorème de
non-atteignabilité de `Bool` en général.

Le filtre d'atteignabilité a maintenant été confronté au **prélude réel**.
`ScratchPreludeReachability.lean` (SHA-256
`4089AA6675FB814BD62AE53A198E537705E8F00C685EFD6525CAB04DAED802C9`)
importe le texte embarqué de ConLeche et exécute ses propres routines de
parsing et de vérification. Ses `#guard` compilés constatent huit records,
un préfixe de sept records accepté avec 23 constantes, le prélude entier
accepté avec 27 constantes — dont le bloc `Bool` complet en tête de
l'environnement final —, puis `reduceBool` accepté comme 28e constante.
Le même diagnostic vérifie que `Bool.false` a exactement le type stocké
`Bool` et que ce dernier n'a aucun paramètre de niveau. **Ces gardes sont
des tests exécutés, pas des théorèmes noyau** sur le parsing du fichier
embarqué ; un essai de `by decide` sur leur résultat ne réduit pas dans le
noyau et n'est donc pas retenu comme preuve.

Un raccord propositionnel compilé figure dans
`ScratchCheckedBoolProjection.lean` (SHA-256
`2B2BAD34A3D849CACA2E51F6A2A37E9B3D457149A75CE09E2B6275DBD958CA70`).
`storedBoolInhabitantExcludesBadBody` montre qu'une `TerminalSlice` dont
l'environnement stocke un habitant de type `Bool` **ne peut pas** utiliser
pour `Bool` la feuille `badValidBody` du séparateur singleton : cette
feuille se lit comme `empty`, alors que `mem_type` du constructeur
imposerait une appartenance à `empty`. C'est une exclusion du **témoin
précis**, pas de toute feuille Bool invalide. `checkedHasProjectedValidBool`
et `checkedSourceSuppliesPinnedBoolRows` montrent séparément que le témoin
projeté du modèle réellement fourni par `FullyChecked` possède la validité
Bool et, sous le même `ReducePinRun`, fournit les lignes épinglées
`hAvalid` et `hTaOk`. `projectedBoolCannotReadBadBody` interdit l'accord
de ce témoin produit avec la mauvaise feuille du séparateur. Ces énoncés
sont conditionnels à `FullyChecked`/au run ou à la présence d'un habitant
stocké ; ils ne transforment pas à eux seuls les `#guard` du prélude en
preuve noyau d'une instance particulière. Les audits n'indiquent que les
trois axiomes hérités de ConLeche, sans `sorryAx`.
`nonemptyInvalidBoolCandidate` vérifie que l'obstruction de l'habitant
stocké n'est pas une preuve déguisée d'`AnnotValid` : `badBit` est bien
dénoté et invalide, mais sa lecture admet un témoin `pt`. Cela ne construit
encore ni les lignes des deux constructeurs dans le vrai environnement,
ni la ligne du recursor, ni une `TerminalSlice` globale.

Cette question a maintenant une réponse positive **uniforme**, plus forte
qu'une réparation ad hoc des constructeurs Bool. Les scratches externes
`ScratchSemanticSpoil.lean`, `ScratchSpoilReads.lean` et
`ScratchCheckedSpoiledBool.lean` construisent une transformation d'une
feuille annotée quelconque `e` en une application à argument mort dont
l'interprétation vaut toujours celle de `e`, qui reste `WellDenoted` si
`e` l'était, mais dont `AnnotValid` est impossible. En l'appliquant
uniquement à la feuille `Bool` d'un `EnvModel`, la construction préserve
`EnvModel` puis **toute** `TerminalSlice` : chaque type stocké se lit encore
et chaque appartenance `mem_type` reste vraie, y compris pour les
constructeurs et le recursor du prélude complet. Le lemme
`denoteMeta_spoilBool_rel` couvre toutes les formes d'expression de
`denoteMeta` : à tout `ψ` et toute profondeur, les deux lectures échouent
ensemble ou réussissent avec des interprétations égales sous tout `ρ`.
Ce n'est donc pas une simple égalité sur quelques constantes testées.

`checkedHasRichOk` extrait du vrai `installRun_model` les deux composantes
`EnvModelM` et `EtaFamiliesClosed` pour tout `FullyChecked .verified`.
Sur **ce même environnement issu du fold**, `checkedHasSpoiledWalk`
construit un `WalkWitness` faible alternatif avec feuille `Bool` invalide ;
`checkedHasSemanticallyEqualInvalidSlice` met côte à côte la projection
riche et la slice faible, égales sur toutes les interprétations des
constantes et sur les lectures sémantiques de toute expression, mais
opposées sur `AnnotValid` de `Bool`. Sous **le même** `ReducePinRun`
épinglé, `checkedPinDistinguishesHistoricalWitness` produit un bon témoin
issu du fold et un mauvais témoin faible avec les mêmes interprétations,
qui satisfont respectivement et réfutent `hAvalid` de la valeur ;
`checkedPinHasSpoiledWitness` réfute aussi `hTaOk` pour ce dernier.
Le caractère non vide de cette situation sur le prélude embarqué et son
`reduceBool` reste attesté par les `#guard` exécutables ci-dessus, **pas**
encore par un théorème noyau instanciant `FullyChecked` sur ces huit records.
Le résultat conditionnel, lui, est un théorème noyau pour tout
`FullyChecked` et tout pin run correspondants. Il distingue donc
rigoureusement « environnement historiquement atteint » et « témoin
faible historiquement produit » : la première propriété tient, la seconde
est fausse pour la slice camouflée. Il ne démontre ni l'échec de stabilité
faible de `B0W`, ni qu'une capacité syntaxique doit persister sous cette
forme, ni une réduction uniforme de l'hypothèse d'univers.

Les trois fichiers externes compilent sous Lean `v4.33.0` contre le commit
épinglé. SHA-256 respectifs :
`020F3A3B5BEFDF911C650B48C4E5B5D8442F7E6EEC5EDC6AE502E0A3B8D41007`,
`693D237099080D85A36CF07CDFA21D1B15D22602D90F02938570B5192C00D6A7`,
`1CF60B8780D5207DB61EA1AFD6C8E6635E5852B215521C6D6E5A305A61A12BEB`.
Leurs audits ne signalent que les trois axiomes hérités de ConLeche,
sans `sorryAx`. Aucun `B1` n'est ainsi justifié : le prochain test doit
chercher quelle donnée constitutive du producteur réel, plus faible que
`acval_validV` global si possible, exclut exactement cette substitution
annotation-invalide tout en fermant la ligne `hAvalid` consommée.

Ce dernier test devait cependant être précédé d'une vérification plus
fondamentale : **`hAvalid` est-il seulement nécessaire à la conservation
terminale spécialisée ?** `ScratchReduceBoolTerminalRows.lean` répond
**non sur l'occurrence épinglée testée**. Le théorème
`reduceBoolTerminalRows` construit directement `valueWellDenoted` et
`valueInDeclaredType` depuis une `TerminalSlice` quelconque et le vrai
`ReducePinRun`, sans `AnnotValid` ni `hTaOk`. Il garde la même feuille
`Bool` dans le domaine et le codomaine du `piR`, puis utilise son
`WellDenoted` et son invariance sous `ρ` déjà présents dans `base2`.
`boolWeakEnvTerminalSuccessor` applique les lignes au vrai
`DeclOpaqueRun` du séparateur, et `boolWeakEnvWalkSuccessor` ajoute le
transport eta par le vrai `DeclRun`. Le séparateur conjoint
`boolWeakGradeFailsButTerminalWalkContinues` exhibe alors **un même vieux
témoin** pour lequel `hAvalid` du certificat riche est faux mais un
`WalkWitness` terminal successeur existe sur la déclaration acceptée.
Cela réfute la conclusion hâtive « grade non reconstructible, donc grade
à persister dans l'invariant no-False ». Le grade peut être nécessaire à
`reduceOps_install` sans être nécessaire à cette extension de
`TerminalSlice`. `pinnedBoolOpaqueTerminalSuccessor` étend la preuve à
tout `DeclOpaqueRun` épinglé dont les deux sorties d'annotation sont
exactement les termes pinned ; ces deux égalités restent des hypothèses
explicites et ne sont pas attribuées automatiquement à tout run.
`checkedSourceSpoiledWalkContinues` applique ce raccord à tout
`FullyChecked` source et au même `DeclOpaqueRun` : un témoin faible
annotation-invalide existe et possède malgré cela un successeur
`WalkWitness` terminal. Un `#guard` supplémentaire sur le prélude
embarqué confirme par exécution, au fuel `50`, les deux égalités
d'annotation sur son environnement accepté ; il ne remplace pas leur
preuve noyau pour ce prélude particulier. Le scratch compile sous Lean
`v4.33.0`, SHA-256
`5B2AFAFD14F6F182CB3413DA573BF6A97A1757110EC2748C56FD678FC9B978A0`,
avec seulement les trois axiomes hérités, sans `sorryAx`.

Les deux hypothèses de sortie annotée viennent ensuite d'être
**reconstruites** à partir du producteur opérationnel, plutôt que
simplement supposées. `ScratchBoolAnnotationGeneral.lean` extrait du
`ReducePinRun` la déclaration `Bool` réellement stockée, ses paramètres
vides, son type `Sort 1` et le fait qu'elle n'est pas une table de
projection. À fuel `50`, `boolTypeAnnotation50` et
`boolValueAnnotation50` suivent la branche réelle de `annotateCore`,
y compris `typeSortPW` et `proofPW`, jusqu'aux deux résultats pinned.
`annotateCore_mono` étend ces sorties à tout fuel `F ≥ 50` ; puis
`checkedSourceSpoiledWalkContinues_ge50` ne requiert plus que
`FullyChecked`, le vrai `DeclOpaqueRun` et cette borne de fuel. Il
construit un vieux témoin faible invalide mais un successeur terminal
sur ce **même** run. Plus fort, les quatre monotonicités opérationnelles
de `ConstantValRun`, `ValueFrontRun`, `ReducePinRun` et `DeclOpaqueRun`
sont prouvées séparément ; `checkedSourceSpoiledWalkContinues_anyFuel`
relève donc **tout** vrai run à `max 50 F` et supprime la borne de fuel
de l'énoncé final. La constante 50 n'est qu'une borne suffisante dans
la preuve interne, non une borne minimale revendiquée. Le théorème
reste conditionnel à `FullyChecked` et au vrai run correspondant ; les
`#guard` du parsing embarqué n'ont toujours pas été transformés en
preuve noyau d'une instance particulière. Le résultat de branche est
encore plus général : `pinnedBoolOpaqueTerminalSuccessor_anyFuel` et
`pinnedBoolOpaqueWalkSuccessor_anyFuel` construisent un successeur
terminal pour **toute** ancienne `TerminalSlice` ou `WalkWitness` faible
et **tout** `DeclOpaqueRun` vérifié de la valeur pinned `reduceBool`, à
fuel quelconque, sans `FullyChecked` ni `EnvModelM`. Il s'agit d'une
stabilité faible effective pour **cette famille d'occurrences**, et non
d'une stabilité historique du témoin ni d'une clôture de toutes les
branches `DeclRun`. Le scratch compile contre ConLeche épinglé, SHA-256
`AD3EFAA90F989B99A24EDB18358394F2125F454F3C050BB559CEFB961C809351`,
sans `sorryAx`, avec les trois axiomes hérités.

Le test symétrique sur **`reduceNat`** est maintenant fermé indépendamment.
`ScratchReduceNatTerminalRows.lean` prouve la lecture de la valeur identité,
les deux lignes exactes de `CheckedValueLocalRows`, puis les sorties annotées
à fuel `50` depuis le `Nat` stocké imposé par `ReducePinRun`. La monotonie
du checker relève tout `DeclOpaqueRun` accepté à `max 50 F` :
`pinnedNatOpaqueTerminalSuccessor_anyFuel` et
`pinnedNatOpaqueWalkSuccessor_anyFuel` construisent un successeur terminal
pour tout ancien témoin faible et tout run opaque vérifié de la valeur
épinglée, sans borne de fuel dans l'énoncé. SHA-256
`033FDC8F19689C52DF8E7FBA07E103E75E53C60EE4EE3C4B4FC890DC516845A6`.

`ScratchReducePinnedTerminalBranch.lean` assemble exactement les deux noms
de `reduceOpNames`. Pour `c ∈ reduceOpNames`, la déclaration opaque brute
`reduceOpRaw c` portant `reduceDeclPin c` conserve la slice terminale et
l'existence d'un `WalkWitness` au travers du vrai `DeclOpaqueRun`, à fuel
arbitraire. Cela ne traite ni toute déclaration opaque, ni une valeur
arbitraire, ni la compatibilité historique du successeur. SHA-256
`B3736E5E47451D85C15AF3DB890543FACDD9117B60C0C2E7B04A85E28CD0C6B0`.

Le consommateur axiomatique suivant est raccordé au **vrai**
`DeclAxiomRun` dans `ScratchOfReduceActualRun.lean`. Pour `ofReduceNat` ou
`ofReduceBool`, les trois autres voies du run sont exclues par leurs gardes.
`ofReduceActualRunWalkSuccessor` construit un successeur faible si l'ancien
témoin fournit `StoredEqValueAtUniverseOne` et l'identité sémantique de
l'opération stockée. Ces deux prémisses restent **explicites** : elles ne
découlent pas de `B0W` ni de la seule acceptation du run. Le transport de ces
capacités le long du fold reste à fermer. SHA-256
`84EA190A4CE25894851E5B3F7A85AEB9990C381B780E4F594B4D0218ED0DC13D`.
Les trois nouveaux scratches compilent sous Lean `v4.33.0` ; leurs audits
ne donnent que les trois axiomes hérités de ConLeche, sans `sorryAx`.

La production de la capacité `Eq.{1}` est maintenant raccordée au **vrai
bloc entier** `DeclBasisRun eqK` dans `ScratchEqBasisRunPrefix.lean`.
`TerminalSlice.consEq`, `TerminalSlice.consEqRefl` et
`TerminalSlice.consEqRec` construisent successivement les trois feuilles
canoniques depuis les seules données terminales précédentes et les fraîcheurs
du `BasisInstallRun` effectif. À chaque passage, la loi
`StoredEqValueAtUniverseOne` est produite puis transportée sur **la même**
réalisation choisie ; les lectures exactes de `Eq` et `Eq.refl` sont gardées
sur le préfixe uniquement parce que la construction de `Eq.rec` les consomme.
Le théorème `eqBasisRunTerminalSuccessorWithEqLaw` fournit ainsi
`Nonempty { next : TerminalSlice V .verified env₂ //
StoredEqValueAtUniverseOne next }` à la sortie du vrai bloc, sans copier
`EnvModelM` ni transporter la loi de recursor du modèle riche. Cela ne prouve
pas encore la conservation de cette capacité dans **toutes** les transitions
qui suivront. `eqBasisRunWalkSuccessorWithEqLaw` ajoute le transport eta par
le vrai `DeclRun` et garde la loi sur **le même témoin** successeur, dans
`Nonempty { next : WalkWitness ... // StoredEqValueAtUniverseOne next.slice }`.
SHA-256
`CFF4E5D9DB1876CB040C6721C7D172D76A5F9EE7ECE78C0D31E11E157F6976C9`.

Le test non vacuitaire suivant a également compilé dans ce même scratch :
`eqBasisRunTerminalSuccessorWithEqLawAndIdentityMap` conserve les lignes
`StoredReduceIdentity` **déjà** établies à travers les trois `cons` réels
du bloc `Eq`. Le transport se fait via la fraîcheur effective, l'équation
`acvalWith` de chaque successeur canonique et le fait que `Eq`, `Eq.refl`,
`Eq.rec` ne sont pas des noms d'opérations reduce. Il n'utilise pas une
nouvelle réalisation arbitraire ni `EnvModelM`. Ce bloc produit la loi
`Eq.{1}` ; il **ne produit pas** les identités reduce qu'il transporte.

Le premier transport après ce bloc est désormais fermé sans substituer un
nouveau modèle arbitraire. `ScratchOpaqueEqLawTransport.lean` reprend le
successeur canonique de `TerminalSlice.preserveOpaqueLocal` et expose, dans
un `Nonempty` propositionnel renforcé, que sa feuille `Eq` coïncide avec
celle de l'ancien témoin dès que la déclaration opaque fraîche ne s'appelle
pas `Eq`. Le théorème ne demande que `OpaqueLocalSupport`, soit les lignes
terminales déjà isolées ; il ne postule aucune nouvelle loi sémantique.
`ScratchPinnedReduceEqLaw.lean` instancie ce transport sur les deux **vrais**
runs opaques pinned `reduceNat` et `reduceBool`, avec l'annotation reconstruite
et le fuel arbitraire. `pinnedReduceWalkPreservesEqLaw` produit un même
successeur faible portant encore `StoredEqValueAtUniverseOne`, eta comprise.
La capacité `Eq.{1}` est ainsi **produite au bloc `eqK` puis transportée
historiquement à travers ces deux transitions réelles**. Elle n'est pas
encore prouvée stable sur toutes les autres familles de `DeclRun`.
SHA-256 :
`826A51DA8DCAC6BC5F5F7C4286C07517B605E1AECAE35BDEAE6F8F633D37BCFF`
et
`4EC584D5E3B75F08DBC870208F83BB29A6D888F6202C2A37D009CD2F3F2528F3`.
Les deux scratches compilent sous Lean `v4.33.0`, sans `sorryAx` ; leurs
audits affichent seulement les trois axiomes hérités de ConLeche.

La seconde capacité consommée par `ofReduce*` est maintenant fermée sur
la même paire de transitions. `ScratchPinnedIdentityLocal.lean` prouve
directement que les valeurs pinned Nat et Bool agissent comme l'identité sur
leur type d'éléments, depuis la lecture du `ReducePinRun` et l'appartenance de
l'argument. Son lemme `StoredReduceIdentity.cons_reduce_of_localIdentity`
montre que cette seule loi locale, sans certificat sémantique global, étend
les identités déjà stockées par le `cons` canonique.
`ScratchPinnedIdentitySuccessor.lean` raccorde le résultat au vrai
`DeclOpaqueRun` : **le même** successeur de `TerminalSlice`, puis de
`WalkWitness`, possède simultanément `StoredEqValueAtUniverseOne` et
`StoredReduceIdentity`. L'assignation exacte `acvalWith` est portée par le
certificat, ce qui interdit de changer silencieusement de réalisation entre
ces deux preuves. Enfin, `ScratchOfReduceFromStoredIdentity.lean` extrait
du vrai `DeclAxiomRun` le guard `ofReduce*`, en déduit l'identité locale depuis
`StoredReduceIdentity`, puis ferme le chemin de **deux transitions réelles**
`pinned reduce → ofReduce*` à partir d'un vieux témoin muni des deux
capacités. Il n'y a ni prémisse `EnvModelM`, ni `DefEqClaim`, ni nouveau
carrier `B1` dans cette composition. La production et la conservation de ces
capacités sur **toutes** les déclarations précédentes et suivantes restent
des obligations distinctes.
SHA-256 respectifs :
`9E66BBB7C4D80B6622948E76E504403CCB7B346EDA368B04581DF6ACB366B06B`,
`42428CDDC81F3C82EB5D83DD81C0C85D919EA277548DD776B809252BC981E5A6`,
`8C828E4D5302D86FDE4620F26EFFE73F3102512B234DE12BE7C9A95251510225`.
Compilation Lean `v4.33.0` ; audits sans `sorryAx`, seulement les trois
axiomes hérités de ConLeche.

`ScratchEqBasisEmptyReduce.lean` raccorde maintenant **trois vraies
transitions** sous une condition de préfixe explicite : aucun nom
`reduceNat`/`reduceBool` n'est stocké avant le bloc `Eq`. Le vrai
`DeclBasisRun eqK` conserve cette absence ; `StoredReduceIdentity` est alors
vraie par vacuité sur **le même** successeur qui porte la loi `Eq.{1}`.
Le vrai `DeclOpaqueRun` pinned installe ensuite la loi d'identité locale et
transporte les deux capacités sur un successeur commun ; le vrai
`DeclAxiomRun ofReduce*` les consomme. Le théorème
`eqBasisThenPinnedThenOfReduceWalkSuccessor` compile avec ces runs et sans
`EnvModelM` ni `DefEqClaim` comme prémisses. Il ne prétend **ni** que la
condition d'absence découle de `B0W`, **ni** que ces transitions sont
consécutives dans tout `FullyChecked`, **ni** que les éventuelles déclarations
intercalées conservent déjà les deux capacités. La vacuité initiale n'est
pas une loi sémantique d'une opération installée.

Le résultat plus fort du **même** fichier ne demande plus cette absence :
`eqBasisRunWalkSuccessorWithEqLawAndIdentity` transporte une identité reduce
ancienne par le vrai `DeclBasisRun eqK`, et
`eqBasisThenPinnedThenOfReduceWalkSuccessorOfIdentity` compose ensuite les
trois transitions réelles. Le seul prémisse historique supplémentaire avant
`Eq` est `StoredReduceIdentity old.slice.base2`. Ce n'est ni une preuve que
`B0W` le reconstruit, ni une fermeture du fold complet. L'ancienne version
fondée sur l'absence reste un corollaire utile pour les préfixes où les
opérations ne sont pas encore installées. SHA-256 du fichier **actuel** :
`3A7D7F54DD6C2E3FA8FA163B11A5298464DFF82429E2258A1D2C2C245CFD54BB`.
Ses six audits n'affichent aucun `sorryAx` ; ils ne rapportent que les trois
axiomes hérités de ConLeche.

Contrôle de reproductibilité : le `.olean` importé de
`ScratchOfReduceClosure` s'est avéré plus ancien que son source. Après
reconstruction de `ScratchChoiceSupportTransport`, les **65** modules
`Scratch*` de la fermeture transitive des huit raccords récents ont été
recompilés en ordre topologique avec le toolchain ConLeche épinglé. Résultat :
65/65 réussis, aucun `sorryAx` dans les audits affichés. Le raccord
`ofReduceActualRunWalkSuccessor` et le préfixe initial `Eq` ont ainsi été revérifiés
contre les interfaces régénérées, pas contre les anciens `.olean`. Cela ne
modifie ni le statut des trois axiomes hérités de ConLeche, ni la portée
conditionnelle des théorèmes. Le nouveau raccord à trois transitions a
ensuite été compilé contre ces artefacts régénérés.

Les prochains tests séparent **deux objectifs** : fermer le transport de
`TerminalSlice` depuis les seules lignes consommées pour les autres
transitions ; étendre le transport désormais construit de la loi `Eq.{1}`
aux autres familles de déclarations réellement traversées ; déterminer
comment l'identité reduce consommée par `ofReduce*` est produite et
transportée. Ni la non-reconstruction de
`hAvalid` depuis `B0W`, ni sa production par le fold riche ne suffisent
isolément à la promouvoir dans `B1`. Les sorties annotées et les deux
branches pinned reduce sont déjà fermées, pas des hypothèses à retester.

La prochaine expérience générique ne doit donc pas installer `BitAgree`
dans le carrier : elle produit localement `hAvalid`, mais ne découle même
pas de la conjonction des lignes positives et du certificat sur l'occurrence
δ, et n'a pas été démontrée nécessaire pour la conservation de la slice.
Repartir des prémisses exactes
de `reduceOps_install` et tester la reconstruction de leurs lignes **pour
un run opaque arbitraire**, sans déduire cette uniformité des seuls exemples
δ, β et ι. Si une donnée historique supplémentaire résiste, la séparer sur
un témoin concret avant d'envisager sa persistance. Les
occurrences β et ι traitées éliminent `hAok` et `hAvalid` comme résidus sur
**ces deux sources exactes** ; elles ne remplacent pas le test universel
sur les autres formes acceptées.
Les lignes encore ouvertes et le grade doivent rester testés séparément depuis
`B0W + DeclOpaqueRun`, avec le même `value'` annoté, avant le passage de la vérification
`isDefEqCore` à sa conséquence sémantique.
Un échec de preuve n'établira aucune non-reconstructibilité : il faudra un
séparateur constructif avant de renforcer le carrier.
Le séparateur antérieur `pdenoteSeparator` réfute déjà la reconstruction de
la bonne dénotation d'une valeur depuis `B0W + ValueFrontRun` sur une
définition acceptée, mais **ne** réfute **pas** automatiquement cette ligne
dans la sous-classe plus étroite des installations reduce munies de leur
`ReducePinRun`. Le filtre du certificat doit donc rester explicite.
Un essai de contre-modèle réduisant la bonne dénotation d'un ancien alias
stocké a été rejeté par la prémisse `Aok` de `TerminalSlice.cons` : `base2`
porte déjà la bonne dénotation des lectures des constantes stockées. Cet
essai n'est pas un séparateur ; une éventuelle rupture de `hAok` doit venir
de la composition d'une nouvelle expression acceptée, pas d'une constante
ancienne arbitrairement mal dénotée.

L’ordre obligatoire est désormais :

1. ouvrir le producteur sémantique du certificat d'un `ReducePinRun` générique
   dans l'ordre réel de `reduceOps_install` : les lectures et leur
   coindexation sont fermées ; `hAok` est fermé pour une valeur constante,
   et les occurrences composées β et ι sont des tests positifs exacts, non
   un théorème générique. Sur l'occurrence δ acceptée, les deux séparateurs
   montrent indépendamment `hAvalid` sans certificat et certificat sans
   `hAvalid`, toujours dans la classe des `B0W` faibles. Tester les
   composantes de `hAok`, `hAvalid`, `hmemA` et du grade de
   l'application pour un run opaque **arbitraire** ; `hTaOk` est déjà
   reconstruit uniformément pour `reduceNat`, tandis que pour `reduceBool`
   il est exactement équivalent à la validité de l'ancienne feuille Bool,
   maintenant séparée sur une déclaration opaque `reduceBool` effectivement
   acceptée depuis un environnement explicite (sans atteignabilité initiale
   revendiquée). Sur la valeur épinglée exacte, `hAvalid` a la même
   équivalence et reconstruit `hTaOk` ; compter ce résidu une seule fois.
   La fermeture locale du sous-but applicatif de niveau `1` sans `hTaOk`
   ne généralise pas encore à tous les metadata et toutes les valeurs
   acceptées. Tester si la capacité restante se reconstruit sur les seuls
   préfixes atteignables et les seules réalisations produites par le fold,
   poursuivre dans l'ordre des consommations réelles, et n'aborder
   qu'ensuite le passage `isDefEqCore` à sa
   conséquence sémantique ; ne pas réintroduire `InferClaim` ou
   `DefEqClaim` comme primitives, et ne pas inférer l'uniformité des seuls
   cas δ, β, ι compilés ;
2. affaiblir `AcvalDefnReadableAppAgreement` lui-même seulement si la preuve
   générique en consomme moins, puis construire un séparateur avant toute
   revendication de stricte faiblesse ou de persistance ;
3. si cette capacité demeure nécessaire, prouver sa conservation sur les
   transitions réelles et distinguer sa donnée productrice de son interface
   exportée ; ne pas remplacer ce travail par le stockage des identités des
   seuls reduce déjà installés, désormais séparé comme insuffisant ;
4. transporter `StoredEqValueAtUniverseOne` dans les branches réelles et le fold,
   puis le raccorder au parcours cached de `FullyChecked` ; cette interface plus
   forte remplace l'ancienne capacité limitée à `propext`, elle ne s'y ajoute pas ;
5. le raccord conditionnel de l'identité et de la loi `Eq.{1}` au vrai
   `DeclAxiomRun` `ofReduceNat`/`ofReduceBool` est fermé ; il reste à
   produire et transporter ces deux prémisses depuis l'histoire constituée,
   sans les supposer depuis `B0W` ;
6. raccorder les quatre sous-branches axiomatiques désormais fermées au dispatch
   `DeclRun`, puis reprendre la boucle au premier résidu concret suivant ;
7. ne parler d'un enrichissement de carrier qu'après nécessité transitionnelle,
   non-reconstructibilité locale et portée d'atteignabilité établies séparément.

Les branches ι `.plain` supplémentaires et `.nested` ne sont pas des tâches
immédiates. Le seul retour à ι autorisé à ce stade est l'occurrence identité
précise qu'a imposée le certificat reduce ; elle est désormais fermée. Les
autres branches ne seront rouvertes que si un nouveau résidu concret de la
fermeture les rend nécessaires.

L’absence de construction n’est jamais une preuve d’impossibilité.

### Gate 5c — réalisation finie des demandes d’univers

#### Constat exact dans ConLeche

L’interface actuelle `SetTheory` fournit une chaîne globale :

```text
univChain : Nat → V
univChain_mem
univChain_tg
```

`univ` utilise cette chaîne aux niveaux positifs. `EnvModelM` quantifie ses
propriétés principales sur toutes les valuations `ψ : Name → Nat` et `ρ` ;
`EnvModelOk = Nonempty EnvModelM ∧ EtaFamiliesClosed` est transporté par
`declStep_preserves` dans le fold. Le capstone `no_constant_of_emptyPin`, lui,
n’exploite finalement qu’une instance très particulière, avec la valuation de
niveaux constante zéro et la valuation ensembliste vide.

La dépendance à la chaîne globale entre donc dans la construction inductive du
modèle, pas dans la dernière inférence `slice → no False`.

#### Objectif admissible

Construire, si les preuves le permettent, la factorisation suivante :

```text
histoire finie d’occurrences de demandes concrètes
        ↓ clôture constitutive des niveaux requis
histoire finie de support
        ↓ réalisation exacte
tour finie suffisante
        ↓ fermeture sous les transitions réellement admises
slice terminale
        ↓
no False
```

La revendication cible est relative :

> Pour toute histoire finie de demandes d’univers concrètes dont la couverture,
> la clôture de support et la stabilité historique ont été construites, une
> réalisation exacte par une tour finie suffit au transport des obligations
> nécessaires à `no False`.

Le raccord supplémentaire affirmant que toute vérification acceptée produit une
telle histoire doit être prouvé séparément. La revendication complète ne doit
être publiée que si chaque flèche est construite.

#### Interdits méthodologiques

Ne jamais utiliser les raccourcis suivants :

```text
flux syntaxique fini
  ⇒ borne de toutes les valuations ψ

entier maximal k
  ⇒ histoire exacte des demandes

longueur de l’histoire des usages
  ⇒ hauteur de tour suffisante

slice terminale suffisante
  ⇒ invariant stable sous DeclRun

Nonempty d’un modèle à chaque état
  ⇒ transport historique d’un même modèle

preuve pour chaque k fixé
  ⇒ fonction interne uniforme construisant toute tour finie
```

Le premier raccourci est particulièrement faux dans l’architecture actuelle :
un fichier fini peut contenir des déclarations polymorphes, tandis que
`EnvModelM` demande des propriétés pour toute fonction `ψ : Name → Nat`.

Le troisième raccourci confond multiplicité des usages et hauteur des niveaux.
La hauteur doit être lue sur une histoire de support fermée : une demande de
niveau élevé peut créer plusieurs étapes de support, tandis que plusieurs
occurrences au même niveau peuvent réutiliser une seule étape.

#### Structure à réemployer

Deux couches doivent être représentées sans les identifier :

```text
U = histoire des usages
    occurrences sémantiques distinctes des demandes

S = histoire de support
    niveaux successifs nécessaires à leur réalisation

Adequacy U S
    chaque usage est servi par un niveau de S
```

La relation `Adequacy U S` peut être plusieurs-vers-un : deux usages distincts
peuvent légitimement partager le même niveau de support. En revanche, les
occurrences de `U` restent individuellement adressables et ne doivent pas être
fusionnées.

L’implémentation doit réutiliser :

```text
ExactInternalRealization
  rôles ↔ occurrences exactes à l’intérieur d’une couche

RootedGeneratedHistory
  succession finie et proof-relevant de U et de S

ExactHistoryInterpretation
  réalisation concrète fidèle de S par les étages de la tour

NormativeAdequacy
  accord entre un régime de demandes et une norme autonome portant
  sur les mêmes objets, lorsque cette instanciation est naturelle

BoundaryGenerator / RegimeExit / UniformRegimeExit
  demande résiduelle et possibilité de prolongement
```

Le nombre `k` est ensuite dérivé de la longueur de `S`, pas de celle de `U`. Il
sert de lecture de la construction ; il n’en est ni l’origine ni le substitut.
Si l’encodage exact des demandes d’univers dans le carrier homogène de `History`
devient artificiel, un adaptateur spécialisé doit préserver ces mêmes lois sans
modifier le noyau général.

Le rôle résiduel représente la prochaine demande effectivement présentée, pas
l’obligation de réaliser dès maintenant tous les niveaux futurs. La continuation
positive de type `oneStepAfterPerimeter` doit être déclenchée par une nouvelle
occurrence, puis l’histoire finie obtenue doit rester exactement traçable.

#### Sous-gates obligatoires

##### 5c.0 — gel de la dépendance actuelle

1. épingler le commit ConLeche et les fichiers exacts de `SetTheory`, `Univ`,
   `EnvModelM`, `Fold`, `Capstone` et `InstalledC` ;
2. enregistrer les signatures réellement consommées ;
3. produire un graphe de dépendance séparant construction du modèle, transport
   par le fold et extraction terminale ;
4. ne pas modifier le checkout externe pendant les tests confirmatoires.

##### 5c.1 — slice terminale et demande observée

1. reformuler exactement l’usage terminal de `univ` par `no False` ;
2. prouver la projection depuis le modèle riche vers cette slice ;
3. conserver la valuation constante zéro comme occurrence explicite, pas comme
   justification d’une borne globale ;
4. vérifier par séparateurs quelles composantes terminales restent nécessaires.

##### 5c.2 — langage des demandes et couverture exacte

1. distinguer expression de niveau symbolique, valuation `ψ`, niveau naturel
   évalué et étage de support ;
2. définir la plus petite famille de demandes concrètes distinguant au moins
   niveau évalué, position, déclaration et consommateur sémantique ;
3. définir les occurrences depuis les appels réels de `univ` ou des interfaces
   qui les consomment ;
4. construire les deux sens rôle d’usage ↔ occurrence sur le périmètre étudié ;
5. construire la clôture de support requise par chaque niveau demandé, y compris
   les étages intermédiaires nécessaires ;
6. construire `Adequacy U S` sans imposer une bijection usage ↔ étage ;
7. prouver couverture et absence de fusion indue des occurrences d’usage ;
8. construire un séparateur pour toute projection qui oublie une détermination
   ensuite requise.

La construction doit d’abord produire l’histoire et ses identifiants, puis
installer les demandes évaluées au moyen d’un `OccurrenceReadout`. Les
aller-retour `perimeterReadout` / `occurrenceReadoutOfPerimeter` et, lorsqu’une
réalisation concrète intervient, `pullbackReadout` / `pushforwardReadout`, sont
les adaptateurs de référence. Ils ne dispensent jamais de prouver séparément
l’adéquation de la valeur lue à l’occurrence source. Une bijection alternative
peut satisfaire les mêmes aller-retour ; la canonicité requiert donc le raccord
structurel fourni par l’accord d’occurrences du producteur.

Une simple collecte syntaxique des `Sort` n’est pas une couverture sémantique.

Le premier test décisif de cette sous-gate est de déterminer si la preuve
spécialisée à `no False` peut remplacer les champs universels en `ψ` par les
seules valuations effectivement consommées. Si le résultat reste paramétré par
une valuation fixée sans raccord vers `FullyChecked`, il constitue une
factorisation conditionnelle, pas une réduction de l’hypothèse du théorème
principal.

##### 5c.3 — fermeture historique sous `DeclRun`

1. partir d’un `WitnessCandidate`, pas d’un invariant déclaré stable ;
2. tester chaque forme réelle de déclaration séparément ;
3. pour chaque obligation rencontrée, classifier : persistante,
   reconstructible localement, terminale ou hors du problème ;
4. arrêter au premier résidu non reconstructible et construire un séparateur ;
5. enrichir le carrier uniquement lorsqu’une persistance est forcée ;
6. établir la stabilité historique avant de projeter vers `Nonempty`.

La procédure doit réutiliser la discipline déjà éprouvée sur δ, β et ι. Elle ne
doit jamais recopier `EnvModelM` sous un autre nom.

##### 5c.4 — réalisation par tour finie

Pour une histoire finie de support fixée, construire positivement :

1. une tour concrète de niveaux suffisante pour toutes ses occurrences ;
2. les relations d’appartenance et de clôture effectivement consommées ;
3. une `ExactHistoryInterpretation` entre rôles de support et étages réalisés ;
4. l’extension d’une tour lorsque le générateur fournit une demande résiduelle ;
5. l’indexation exacte entre `univ n` et `univChain`, y compris le décalage des
   niveaux positifs ;
6. les séparateurs montrant quelles relations ne peuvent pas être oubliées.

Lorsque des correspondances locales exactes avec les étages construits sont
disponibles, tenter d’abord la reconstruction locale-vers-globale exécutable sur
le modèle de `ExactNonClosingRealization.toPerimeterExtension`. L’accord exact
doit fournir l’injectivité comme conséquence, puis la factorisation globale doit
rester une donnée de `Type` calculable. Une preuve propositionnelle d’existence,
une sélection classique ou une définition `noncomputable` ne ferme pas cette
sous-gate. Sur des données closes représentatives, ajouter un test de réduction
ou de génération de code dès que la construction produit un objet calculable.

La frontière des univers de Lean doit être explicitée. Si Lean ne permet pas de
construire une tour arbitraire uniforme dans un même niveau métathéorique, le
résultat admissible est une famille de théorèmes pour chaque hauteur fixée, ou
une interface paramétrée par une tour finie déjà construite. Ce résultat ne doit
pas être reformulé comme une construction interne uniforme.

##### 5c.5 — raccord au fold et au capstone

La gate est fermée seulement si une chaîne de termes Lean relie :

```text
acceptation / FullyChecked
  → témoin historique fini stable
  → réalisation finie exacte
  → slice terminale
  → no False
```

Une projection obtenue depuis le `EnvModelM` global ne ferme pas cette gate :
elle réutiliserait précisément l’hypothèse que l’on cherche à réduire.

##### 5c.6 — comparaison de force

1. montrer que l’interface globale actuelle reconstruit l’interface finie ;
2. chercher un séparateur non vacue au converse dans une classe explicitement
   fixée ;
3. répéter la comparaison dans la sous-classe des histoires atteignables ;
4. distinguer absence de reconstruction trouvée et impossibilité démontrée.

Le mot « réduction » exige au minimum une factorisation complète de la preuve et
une comparaison explicite des hypothèses. Le mot « strictement » exige un
séparateur ou un théorème de non-reconstruction dans une classe annoncée.

##### 5c.7 — lecture numérique dérivée

Une fois `U`, sa clôture de support `S` et leur réalisation construites,
seulement alors :

```text
k := History.length S
```

Prouver que la tour réalisée possède exactement la hauteur utile ou une hauteur
suffisante explicitement reliée à `k`. Ne jamais présenter `k` comme ayant été
déduit d’une simple taille de fichier ou du seul nombre d’occurrences dans `U`.
Formellement, traiter `k` comme une lecture tardive du support déjà constitué :
la construction de `S`, ses occurrences et leur réalisation ne doit dépendre ni
de `k` ni d’une autre annotation numérique obtenue a posteriori.

#### Issues scientifiques admises

```text
construction complète
→ réduction relative établie

factorisation conditionnelle sans instance finie construite
→ interface suffisante, réduction non établie

séparateur contre un candidat
→ candidat réfuté, recherche poursuivie

ni construction ni impossibilité
→ question ouverte
```

### Critère d’arrêt général de la Gate 5

Réduire une sous-gate à une étude documentaire si sa fermeture exige une copie
substantielle du code de ConLeche, une dépendance technique du noyau scientifique
envers ConLeche ou une réimplémentation générale de son checker. Une petite
instanciation externe, isolée et épinglée, reste admise pour tester les
factorisations contre le code réel.

## 11. Gate 6 — composition des statuts

Le résultat final juxtapose, sans les fusionner :

```text
certificat Lean de transport fidèle
+
rapport reproductible d’acceptation par ConLeche
+
résultats de dissection interne effectivement fermés
```

Le certificat Lean peut établir une règle abstraite de transport :

```text
fidélité de la chaîne
+
propriété terminale précisément indexée
→
propriété source-relative précisément indexée
```

La réduction de l’hypothèse d’univers n’entre dans cette composition que si la
Gate 5c.5 est fermée. Avant cela, elle reste un programme de recherche et ne doit
pas modifier la formulation du théorème acquis.

Le certificat ne doit jamais contenir un champ `externalCheckerRecorded`
présenté comme un théorème si ce champ provient seulement de l’exécution du
binaire.

La documentation rassemble les deux résultats et indique leur statut respectif.

## 12. Livrables finaux

### Livrables déjà présents

```text
ConstitutiveAlignment/
  VerificationTransport.lean

scripts/
  run_con_leche_audit.py

audit/
  AUDIT_BUILD.txt

docs/fr/
  audit_constitutif_con_leche.md

docs/en/
  constitutive_con_leche_audit.md
```

Le rapport confirmatoire produit par le script n’est ajouté au dépôt que s’il
est déclaré comme livrable final, de taille raisonnable et intégralement lié au
commit publié. Les sorties volumineuses restent externes et sont identifiées par
leurs empreintes.

### Livrables conditionnels de la Gate 5c

Ne créer un module Lean supplémentaire que lorsqu’une factorisation autonome
compile sans dépendance technique à ConLeche. Son nom doit décrire le résultat
effectivement obtenu — réalisation finie, interface conditionnelle ou
séparateur — et non annoncer par avance une réduction de `univChain`.

Les fichiers de scratch ConLeche, copies de code externe et instruments de
dissection restent hors du dépôt. Seuls un résultat autonome dans le vocabulaire
local, sa preuve, ses audits et sa documentation bilingue peuvent devenir des
livrables.

L’export NDJSON volumineux, les clones externes, les builds, les caches et les
espaces d’extraction ne doivent pas être ajoutés au dépôt.

Le script Python standard est l’implémentation portable unique ; ne pas créer de
wrappers PowerShell et shell redondants. Si un fichier Lean unique suffit, ne
pas créer un fichier de séparateurs supplémentaire.

## 13. Documentation publique

### Message court

```text
ConLeche verifies the checked declarations.
Constitutive analysis tracks how those declarations were formed from the source.
```

### Revendication anglaise admissible

```text
We independently checked the exported development using ConLeche’s verified
mode. Its no-False guarantee is relative to the explicitly stated set-theoretic
model assumption. We separately analyse the provenance boundary between the
source development and the declarations presented to the checker.
```

Tant que la Gate 5c.5 n’est pas fermée, la seule formulation admissible sur les
univers est :

```text
We are investigating whether the global universe-chain assumption can be
replaced, for the no-False result, by a finite realization indexed by the
universe demands actually constituted during verification. No such reduction is
claimed yet.
```

Après fermeture complète seulement, remplacer cette phrase par l’énoncé exact
du théorème obtenu, en conservant ses paramètres, sa classe d’histoires et sa
portée relative.

Éviter absolument :

```text
consistency-proven checker
fully verified end-to-end pipeline
proof of Lean consistency
proof that the whole ConLeche frontend preserves meaning
the omega-chain assumption has been removed
a finite input automatically yields a semantic universe bound
```

Les déclarations d’auteur restent placées à la fin des documents scientifiques,
conformément à la convention du dépôt.

## 14. Vérifications finales

### Lean

- `lake build` réussi ;
- aucune occurrence interdite dans les fichiers Lean ;
- un unique bloc `AXIOM_AUDIT` final par fichier ;
- tous les noms audités existent ;
- chaque `#print axioms` rapporte `no axioms` ;
- aucune obligation concrète remplacée par une hypothèse ouverte.

Les scratchs compilés contre ConLeche peuvent hériter des axiomes déclarés par
ce développement externe ; ils doivent les rapporter exactement. Aucun de ces
scratchs ne peut être transplanté dans le dépôt tant que son audit ne satisfait
pas les règles constructives locales.

### Structure et univers

- toutes les demandes d’univers sont liées à des occurrences réelles ;
- les deux aller-retour de la réalisation exacte sont prouvés ;
- aucune quantification en `ψ` n’a été silencieusement remplacée par une borne
  syntaxique ;
- la fermeture sous chaque `DeclRun` revendiqué est démontrée ;
- la tour finie est construite positivement ou fournie par une interface
  explicitement conditionnelle ;
- `k` est dérivé de l’histoire et non introduit comme substitut de preuve ;
- toute stricte réduction annoncée possède un séparateur dans la classe publiée.

### Audit externe

- commits externes épinglés ;
- toolchains compatibles et enregistrés ;
- export régénéré dans le run confirmatoire ;
- hash calculé avant exécution puis recontrôlé après ;
- mode `--verified` attesté ;
- verdict et code de sortie conservés sans réécriture.

### Documentation

- versions française et anglaise cohérentes ;
- liens locaux valides ;
- statuts `démontré`, `implémenté`, `observé`, `vérifié extérieurement`,
  `dérivé architecturalement` et `ouvert` employés exactement ;
- aucune revendication plus forte que le résultat ;
- README mis à jour seulement si l’audit est effectivement fermé ;
- toute mention de réduction de l’hypothèse d’univers correspond exactement au
  statut de la Gate 5c.5 dans les deux langues.

### Git

- diff final relu ;
- aucun artefact généré, clone externe ou cache suivi ;
- manifeste recalculé depuis l’arbre final ;
- présent document et son dossier de chantier supprimés dans la pull request ou
  merge request vers `main` ;
- fusion et push uniquement sur demande explicite de l’utilisateur ;
- vérifications répétées sur le commit effectivement fusionné dans `main`.

## 15. Ordre d’exécution

```text
acquis à conserver
  Gate 0   compatibilité du socle testé
  Gate 2   script de provenance exécutable
  Gate 3   noyau formel spécialisé
  Gate 4   séparateurs de provenance
  Gate 4b  modèle local de l’alignement R → S
  Gate 5a  cas réel de provenance borné
  Gate 5b  δ gelé + β indépendant + comparaison δ/β

travail immédiat
  Gate 5b  raccord defn atteignable à la capacité δ/β fermé
  Gate 5b  capacité productrice affaiblie et séparateur terminal construits
  Gate 5b  première compatibilité du successeur extraite et séparée
  Gate 5b  suffisance de la compatibilité sur la première transition fermée
  Gate 5b  premier test de définition ancienne sous nouvel argument fermé
  Gate 5b  annotation historique exacte réfutée, représentant alternatif construit
  Gate 5b  transport fermé du nouvel argument `.prf` reconstruit localement
  Gate 5b  successeur exact du premier `defn` construit avec `WalkWitness + provider`
  Gate 5b  représentant ouvert inféré extrait sans `DefEqClaim`
  Gate 5b  second `defn` concret fermé avec slice exacte et provider complet
  Gate 5b  tête fraîche et définition ancienne traitées séparément
  Gate 5b  recontextualisation des seeds fermées prouvée à toute profondeur
  Gate 5b  nouveaux arguments lisibles éliminés comme faux résidu
  Gate 5b  readback factorisé par une seule lecture ancienne du corps
  Gate 5b  lecture du corps frais produite par le seul `ValueFrontRun`
  Gate 5b  accord corps frais / tête installée produit par le vrai cons
  Gate 5b  obligation exacte `StoredDefnBodiesReadable` isolée pour les anciens
  Gate 5b  stabilité de cette obligation sous un vrai cons `defn` prouvée
  Gate 5b  producteur δ affaibli préservé depuis cette seule obligation
  Gate 5b  séparateur construit : `EnvWF + TerminalSlice` ne suffit pas
  Gate 5b  séparateur exclu des sorties de tout vrai `ValueFrontRun`
  Gate 5b  dériver l’obligation le long de l’histoire constituée du fold
  Gate 5b  décider reconstruction locale ou persistance seulement après fermeture
  Gate 5b  ne rouvrir ι que si la fermeture produit un résidu ι concret
  Gate 5b  factorisation locale de `propext` par relations `Iff` et `Eq` fermée
  Gate 5c.3  `StoredIffRecBits` reconstruit sur le fold pur et sur `FullyChecked`
  Gate 5c.3  relation `Eq` locale factorisée, produite directement et séparée de B0W
  Gate 5c.3  certificat reduce isolé, séparé localement et sur environnement atteint
  Gate 5c.3  identités reduce anciennes séparées comme insuffisantes
  Gate 5c.3  raccord positif alias-δ vers le certificat reduce fermé sans DefEqClaim
  Gate 5c.3  certificat reduce β fermé localement depuis B0W sans mémoire nouvelle
  Gate 5c.3  certificat reduce ι identité fermé sur la lecture source exacte
  Gate 5c.3  alias-δ raccordé au vrai DeclOpaqueRun, DeclRun et checkDeclsPure
  Gate 5c.3  β/ι raccordés séparément au vrai DeclOpaqueRun, DeclRun et checkDeclsPure
  Gate 5c.3  quatre lignes β et grade applicatif reconstruits depuis B0W
  Gate 5c.3  quatre lignes ι et grade applicatif reconstruits depuis B0W
  Gate 5c.3  BitAgree tête/corps testé comme producteur local de hAvalid δ
  Gate 5c.3  hAvalid de la valeur constante séparé au premier résidu local
  Gate 5c.3  deux branches pinned reduce fermées terminalement à tout fuel
  Gate 5c.3  ofReduce raccordé conditionnellement au vrai DeclAxiomRun
  Gate 5c.3  loi Eq.{1} produite à la sortie du vrai bloc basis eqK
  Gate 5c.3  loi Eq.{1} transportée avec le même témoin sur reduceNat/Bool
  Gate 5c.3  chaîne réelle eqK -> pinned reduce -> ofReduce fermée sous absence reduce explicite
  Gate 5c.3  même chaîne fermée sans absence, sous identité reduce ancienne explicite
  Gate 5c.3  généraliser ce raccord au certificat de tout ReducePinRun
  Gate 5c.3  tester la conservation des capacités restantes avant tout B1

réduction de l’hypothèse d’univers
  Gate 5c.0  geler les dépendances SetTheory/EnvModel/fold/capstone
  Gate 5c.1  fixer la slice terminale
  Gate 5c.2  construire demandes, occurrences et couverture exacte
  Gate 5c.3  fermer l’invariant historique sous DeclRun
  Gate 5c.4  construire ou paramétrer la réalisation finie
  Gate 5c.5  raccorder FullyChecked à no False sans EnvModelM global
  Gate 5c.6  comparer les forces dans des classes explicites
  Gate 5c.7  dériver la lecture numérique k

clôture
  Gate 1   run confirmatoire sur le commit final propre
  Gate 6   composition documentaire exacte des statuts
```

Cet ordre conserve les cas indépendants avant comparaison, puis traite
l’hypothèse d’univers comme une nouvelle factorisation de preuve. Le run externe
confirmatoire vient en dernier afin de viser exactement l’arbre publié.

Les Gates 5c.0 et 5c.1 peuvent être menées pendant la fin de l’analyse ι, car
elles ne modifient pas ses interfaces. En revanche, la carte des consommateurs
de la Gate 5c.2 ne peut être gelée avant la stabilisation de ι : une obligation
rencontrée dans `.plain` ou `.nested` peut modifier la fermeture réellement
requise.

## 16. Résultats publiables

### Socle déjà visé

Le résultat minimal publiable comprend :

1. un run ConLeche `--verified --jobs=1` reproductible sur un export identifié ;
2. un lien opérationnel vérifié entre commit, export, hash et verdict ;
3. un séparateur Lean constructif entre acceptation terminale et fidélité amont ;
4. une reconstruction du contrat interne `R → S`, distincte de completeness et
   de la fidélité amont ;
5. une étude précisément bornée d’une transformation frontend réelle ;
6. une factorisation suffisante du transport de `no False` et les nécessités
   locales établies par séparateurs dans la famille étudiée ;
7. la factorisation δ/β et le statut borné du séparateur ι `.plain` ;
8. une documentation bilingue distinguant toutes les portées.

Chaque sous-gate conserve son statut propre. L’ouverture de la Gate 5c ne bloque
pas la publication du socle acquis ; elle interdit seulement de revendiquer une
réduction de l’hypothèse d’univers. Une Gate 5a ou 5b ouverte doit être signalée
sans être absorbée par les Gates 1 à 4.

### Extension sur l’hypothèse d’univers

Pour annoncer une réduction relative de la chaîne globale, il faut en plus :

1. une histoire finie d’usages exactement couverte par ses occurrences ;
2. une clôture finie de support adéquate à tous ces usages ;
3. un candidat historiquement stable sous toutes les transitions revendiquées ;
4. une réalisation finie exacte de l’histoire de support ;
5. une factorisation complète jusqu’à `no False` qui ne repasse pas par
   `EnvModelM` muni de la chaîne globale ;
6. une comparaison de force explicitant ce qui a été retiré, conservé ou rendu
   reconstructible ;
7. une documentation bilingue qui distingue théorème uniforme, famille de
   théorèmes à hauteur fixée et interface conditionnelle.

Si un seul de ces points manque, publier le résultat intermédiaire exact —
interface, séparateur ou question ouverte — sans employer « hypothèse réduite ».

## 17. Références externes à figer

- dépôt ConLeche : `https://github.com/leanprover/con-leche` ;
- commit ConLeche étudié :
  `86cd20a65660d757cedc81561a44579099b565d0` ;
- contrat de ligne de commande, hypothèse en théorie des ensembles et limites :
  `OVERVIEW.md` à ce commit ;
- théorème principal : `ConLeche/MainTheorem.lean` à ce commit ;
- modèle ensembliste : `ConLeche/SetTheory/Core.lean` et
  `ConLeche/SetTheory/Derive/Univ.lean` à ce commit ;
- invariant riche et fold : `ConLeche/Model/Annot/EnvModelM.lean` et
  `ConLeche/Model/Fold.lean` à ce commit ;
- capstone et raccord `FullyChecked` : `ConLeche/Model/Capstone.lean` et
  `ConLeche/Verify/Cached/InstalledC.lean` à ce commit ;
- frontière du frontend : `ConLeche/Frontend/ProjRec.lean` et
  `ConLeche/Frontend/ExportC.lean` à ce commit ;
- format et exécutable d’export : `https://github.com/leanprover/lean4export`.

Le rapport final remplace les références de branche par les identifiants de
commit effectivement utilisés.
