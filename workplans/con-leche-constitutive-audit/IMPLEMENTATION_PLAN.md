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
- ι a été lancé indépendamment : le cas `.plain` possède un séparateur réel,
  mais `.nested` et la comparaison postérieure restent ouverts ;
- aucune réduction de l’hypothèse globale de chaîne d’univers n’est encore
  démontrée.

## 1. Principe scientifique

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
  des occurrences vers une réalisation concrète ;
- `ConstitutiveAlignment.InjectiveMap` et `InjectiveMap.trans` pour la
  conservation des distinctions d’occurrences ;
- les transports d’occurrences déjà prouvés dans le Cycle 1 ;
- `ConstitutiveAlignment.Separators.noFaithfulTerminalOnlyRealization` comme
  séparateur générique déjà acquis entre lecture terminale et réalisation fidèle.

`History.length` est une lecture numérique dérivée tardivement ; elle ne doit
jamais remplacer l’histoire ni servir à postuler sa hauteur avant construction.

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
- le séparateur ι `.plain` jusqu’à l’échec relationnel de `headInPiR`.

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
  construits sur des témoins affaiblis.

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

Travail restant, dans cet ordre :

1. poursuivre le weakening de `.plain` jusqu’à stabiliser sa capacité propre ;
2. analyser `.nested` depuis son producteur réel, sans vocabulaire imposé ;
3. stabiliser l’interface ι seulement après les deux branches ;
4. comparer ensuite seulement δ, β et ι ;
5. conclure par construction d’une capacité commune, impossibilité dans une
   classe `K` explicitement définie, ou maintien honnête de la question ouverte.

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
  Gate 5b  fermer ι .plain
  Gate 5b  analyser ι .nested indépendamment
  Gate 5b  geler l’interface ι puis comparer δ/β/ι

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
