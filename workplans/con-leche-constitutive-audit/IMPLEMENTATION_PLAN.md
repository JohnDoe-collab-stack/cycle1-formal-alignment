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

L’ordre obligatoire est désormais :

1. raccorder les occurrences reduce déjà fermées à leur `DeclOpaqueRun`, puis au
   `DeclRun`, sans remplacer les preuves kernel des sous-runs par une simple
   observation exécutable de `checkDecl` ;
2. ouvrir le producteur sémantique du certificat d'un `ReducePinRun` générique
   et tester, sans réintroduire `DefEqClaim` comme primitive, quelles capacités
   δ/β/ι déjà isolées reconstruisent son exécution ; les cas alias-δ, β et
   l'occurrence identité ι compilés sont trois raccords positifs de forces
   différentes, pas encore le théorème uniforme ;
3. affaiblir `AcvalDefnReadableAppAgreement` lui-même seulement si la preuve
   générique en consomme moins, puis construire un séparateur avant toute
   revendication de stricte faiblesse ou de persistance ;
4. si cette capacité demeure nécessaire, prouver sa conservation sur les
   transitions réelles et distinguer sa donnée productrice de son interface
   exportée ; ne pas remplacer ce travail par le stockage des identités des
   seuls reduce déjà installés, désormais séparé comme insuffisant ;
5. transporter `StoredEqValueAtUniverseOne` dans les branches réelles et le fold,
   puis le raccorder au parcours cached de `FullyChecked` ; cette interface plus
   forte remplace l'ancienne capacité limitée à `propext`, elle ne s'y ajoute pas ;
6. raccorder l'identité produite et la loi `Eq.{1}` au vrai `DeclAxiomRun`
   `ofReduceNat`/`ofReduceBool`, puis fermer leur nouvelle ligne terminale ;
7. raccorder les quatre sous-branches axiomatiques désormais fermées au dispatch
   `DeclRun`, puis reprendre la boucle au premier résidu concret suivant ;
8. ne parler d'un enrichissement de carrier qu'après nécessité transitionnelle,
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
  Gate 5c.3  raccorder les cas reduce au vrai DeclOpaqueRun puis DeclRun
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
