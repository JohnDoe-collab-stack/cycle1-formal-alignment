# Plan détaillé — raccord constitutif opérationnel `NP AND/OR P`

> **Statut :** document de chantier temporaire sur la branche de travail.
> Il devra être supprimé avant l’intégration dans `main`, sauf décision explicite
> d’en faire un document scientifique canonique.

> **Périmètre :** ce document porte exclusivement sur l’achèvement interne du
> cadre constitutif `NP AND/OR P`. Il n’introduit aucune obligation de raccord à
> une autre formulation du problème.

## 0. État exact de départ

Légende :

- `[x]` déjà construit et prouvé ;
- `[~]` présent mais à intégrer ou à renforcer ;
- `[ ]` travail restant.

### Fondations constitutives

- `[x]` Production canonique d’un successeur depuis l’état courant :
  `generate : source → Σ target, GeneratedStep source target`.
- `[x]` La cible est produite par `canonicalTarget source`, jamais fournie
  extérieurement.
- `[x]` Provenance, différence fraîche et obstruction de clôture sont conservées
  dans `GeneratedStep`.
- `[x]` Histoires réelles construites par `appendGenerated`.
- `[x]` Itération à toute profondeur naturelle par `iteratedHistory`.
- `[x]` Persistance exacte des occurrences et des distinctions.
- `[x]` Réalisation concrète et naturalité des transports.

Sources principales :

- `StrongPerimetralTurning.lean` ;
- `StrongPerimetralTurning/IteratedConstitutivePersistence.lean` ;
- `StructuralEntrypoint.lean`.

### Recherche et exécution

- `[x]` Séparation entre continuation structurale et acceptation.
- `[x]` Relations primitives et transports préservant l’acceptation.
- `[x]` Syntaxe finie `TransportCode`.
- `[x]` Compilation d’un chemin constitué en code.
- `[x]` Validation locale.
- `[x]` Exécution séquentielle locale.
- `[x]` Exactement une requête primitive par étape.
- `[x]` Zéro candidat de composition globale pendant l’exécution séquentielle.
- `[x]` Comptabilité séparée de production, validation et exécution.
- `[x]` Bornes polynomiales pour la famille explicite déjà formalisée.

Sources principales :

- `ConstitutiveSearch/SearchSystem.lean` ;
- `ConstitutiveSearch/TransportCode.lean` ;
- `ConstitutiveSearch/ConstitutedPrimitivePath.lean` ;
- `ConstitutiveSearch/SAT/TrajectoryConstitutedLocalSchedule.lean` ;
- `ConstitutiveSearch/SAT/TrajectoryConstitutiveSynthesis.lean`.

### Réparation opérationnelle en cours

- `[x]` Deux organisations sur une même entrée et une même formule observable.
- `[x]` Histoires de provenance différentes.
- `[x]` Recherche instrumentée de la relation.
- `[x]` Construction du code uniquement après succès de la recherche.
- `[x]` Application effective du code retourné à une continuation source.
- `[x]` Lecture du bit terminal sur la continuation transportée.
- `[x]` Échec sans code lorsque la provenance ne correspond pas.
- `[~]` Procédure complète encore exposée avec certains paramètres déjà
  sélectionnés.
- `[ ]` Raccord avec le producteur constitutif général.
- `[ ]` Théorème intégré final.

Source :

- `ConstitutiveSearch/SAT/OperationalProjectionInadequacy.lean`.

## 1. Objectif formel final

Construire une procédure unique dont la dépendance causale soit exactement :

```text
entrée
  ↓
état constitutif initial
  ↓
production du prochain état par generate
  ↓
histoire constituée
  ↓
extraction exécutable des candidats
  ↓
recherche exécutable de la relation locale
  ↓
construction du code depuis la relation trouvée
  ↓
validation du code
  ↓
application du code à la continuation source
  ↓
continuation terminale produite
  ↓
lecture terminale
  ↓
décision
```

La fonction publique finale ne devra recevoir que l’entrée :

```lean
executeConstitutiveResolution : Input → ConstitutiveResolutionRun
```

Elle ne devra pas recevoir :

```text
variable utile
cible attendue
relation attendue
code attendu
état terminal attendu
réponse attendue
preuve de succès extérieure
```

Le résultat devra contenir les données calculées, leurs compteurs et les preuves
reliant chaque phase à la précédente.

## 2. Invariants obligatoires

### 2.1 Endogénéité

Chaque objet constitutif doit être produit depuis les données déjà disponibles :

```text
target       depuis source
candidate    depuis état/formule/histoire
relation     depuis source + candidat produit
code         depuis relation trouvée
terminal     depuis évaluation du code
décision     depuis terminal
```

Aucune cible ou relation correcte ne doit être injectée comme paramètre caché.

### 2.2 Causalité matérialisée

Les dépendances doivent apparaître dans les types :

```lean
GeneratedState source
DiscoveryRun generated
DiscoveredRelation discovery
ProducedCode relation
ValidatedCode code
ExecutionResult validated
TerminalArtifact execution
Decision terminal
```

Une simple égalité prouvée après coup ne suffit pas.

### 2.3 Absence de bypass

Il faut rendre impossible dans l’API annoncée :

```text
entrée → reconstruction directe de la cible
entrée → terminal préconnu
entrée → décision copiée
```

Le terminal doit être extrait de la continuation retournée par l’évaluation du
code.

### 2.4 Même entrée, même projection

Les deux constitutions devront d’abord être produites positivement depuis la
même entrée et distinguées par leur genèse, leur histoire ou leur provenance,
sans utiliser leur projection ni leur résultat opérationnel.

L’ordre obligatoire est :

```text
input positif = input négatif
→ construction positive des deux organisations
→ établissement positif de leurs constitutions
→ preuve constitution positive ≠ constitution négative
→ projection positive = projection négative
→ résultat opérationnel positif ≠ résultat opérationnel négatif
→ non-factorisation
```

Le résultat recherché est donc :

```text
constitution positive ≠ constitution négative
et
projection positive = projection négative
et
résultat opérationnel positif ≠ résultat opérationnel négatif
```

Cela élimine l’ancien défaut où les témoins provenaient d’instances disjointes.
L’égalité de projection ne doit jamais servir à constituer ou à distinguer
rétroactivement les deux organisations.

### 2.5 Comptabilité intrinsèque

Les coûts doivent être produits par les récursions exécutées :

```text
visites de clauses
visites de littéraux
visites de décisions
comparaisons de variables
candidats examinés
relations interrogées
atomes de code exécutés
observations terminales
```

Aucun coût ne devra être un nombre choisi après l’exécution.

### 2.6 Conservation du caractère local

La construction ne doit pas réintroduire une recherche de clôture globale.

Le chemin prévu reste :

```text
une étape produite
→ un nouvel état constitué
→ extraction et discovery locales
→ Option relation locale
→ si succès : atome de transport
→ validation et exécution locales
→ étape suivante
```

La non-composabilité globale des schedules de longueur au moins deux demeure un
résultat positif du cadre, pas un défaut à éliminer.

## 3. Phase I — Fermer la réparation opérationnelle sur une même entrée

### But

Transformer `OperationalProjectionInadequacy` en expérience formelle
complètement intégrée.

### 3.1 Conserver les éléments déjà corrects

Réutiliser sans duplication :

- `GeneratedFalsePath` ;
- `generateFalsePath` ;
- `operationalCommonParentPath` ;
- `operationalMismatchedParentPath` ;
- `runInstrumentedFlipSearch` ;
- `executeInstrumentedTransport` ;
- `operationalPositiveRun` ;
- `operationalNegativeRun`.

### 3.2 Supprimer les paramètres présélectionnés de l’entrée publique

`executeInstrumentedTransport` peut rester une primitive interne. La procédure
publique ne devra plus prendre :

```lean
selected
observed
source
target
continuation
```

Une couche supérieure devra les produire.

Forme attendue :

```lean
def runOperationalProjectionExperiment
    (input : Nat) :
    OperationalProjectionExperimentRun input
```

### 3.3 Produire les deux organisations depuis la même racine

Le run doit contenir :

```lean
root
source
positiveOrganization
negativeOrganization
```

avec preuves :

```lean
positiveOrganization.input = input
negativeOrganization.input = input
positiveOrganization.root = negativeOrganization.root
positiveOrganization.constitution ≠ negativeOrganization.constitution
```

La dernière différence doit être établie depuis les constructions elles-mêmes,
par leur genèse, leur histoire ou leur provenance. L’égalité de leurs projections
n’intervient qu’à l’étape 3.5.

### 3.4 Exécuter exactement la même procédure

Les deux branches doivent appeler la même fonction d’exécution. Seules leurs
histoires constituées diffèrent.

Il faudra prouver :

```lean
positiveRun.terminalBit = some true
positiveRun.codeAtoms = 1

negativeRun.terminalBit = none
negativeRun.codeAtoms = 0
```

### 3.5 Établir l’insuffisance de la projection

Cette étape ne commence qu’après établissement positif des deux constitutions et
de leur différence. Définir alors précisément la projection autorisée, puis
prouver :

```lean
project positiveOrganization =
  project negativeOrganization
```

et simultanément :

```lean
operationalOutcome positiveOrganization ≠
  operationalOutcome negativeOrganization
```

En déduire un théorème de non-factorisation sur la même entrée :

```lean
¬ ∃ reconstruct,
    ∀ organization,
      reconstruct organization.input (project organization) =
        operationalOutcome organization
```

Le point décisif est que `input` et `project organization` sont identiques pour
les deux témoins, alors que leur différence constitutive a été établie avant et
indépendamment de cette projection.

### Critère de sortie

La phase est terminée lorsque le résultat opérationnel différent provient de
l’application ou de l’absence réelle du code, et non de deux constantes placées
dans les témoins.

## 4. Phase II — Rendre la discovery entièrement endogène

### But

Éliminer de la procédure publique la variable sélectionnée et la cible correcte.

### 4.1 Réutiliser l’extraction instrumentée existante

Réutiliser :

- `extractClauseCandidateRun` ;
- `extractCnfCandidateRun` ;
- `runCandidateExtraction` ;
- `exploreStructuralCandidates` ;
- les familles de leurres de `GrowingDiscoveryBenchmark`.

### 4.2 Construire un run unifié de discovery

Le run devra contenir au minimum :

```lean
structure OperationalDiscoveryRun where
  extraction : CandidateExtractionRun
  attempts : Nat
  testedCandidates : List Var
  found : Option DiscoveredOperationalRelation
  stats : OperationalDiscoveryStats
```

Les champs devront être calculés ensemble par la récursion.

### 4.3 Faire produire la cible testée

Pour chaque candidat extrait :

1. construire les états locaux candidats depuis l’état courant ;
2. exécuter le chercheur de relation ;
3. conserver la première relation effectivement trouvée ;
4. produire le code depuis cette relation.

La cible correcte ne doit pas être fournie au moteur de discovery comme réponse
attendue.

### 4.4 Conserver une famille de leurres croissante

La famille doit satisfaire :

```text
nombre de leurres         croît avec l’entrée
taille de la formule      croît avec l’entrée
candidat utile            n’est pas le premier
tentatives                croissent strictement
visites de littéraux      croissent strictement
comparaisons              croissent strictement
```

Les théorèmes de `GrowingDiscoveryBenchmark` doivent servir de base, pas être
réécrits.

### 4.5 Déduire la variable observée

Le bit terminal observé doit être dérivé du résultat de discovery ou de la
sémantique de la relation trouvée. Il ne doit pas être un second paramètre
externe indépendant.

### Critère de sortie

La signature publique doit être réductible à :

```lean
input → run
```

et le run doit contenir la variable, la relation, le code et la cible réellement
découverts.

## 5. Phase III — Construire le raccord entre le producteur constitutif et la recherche

### But

Relier formellement les deux architectures actuellement séparées.

L’absence du raccord est confirmée par l’arbre d’imports : aucun module
`ConstitutiveSearch` n’importe actuellement les modules fondateurs.

### 5.0 Maintenir les trois niveaux de l’architecture

Le raccord doit conserver explicitement trois niveaux distincts :

```text
théorie constitutive générale
        ↓ instanciation
instance circulaire de déploiement
        ↓ réalisation construite
instance opérationnelle de recherche
```

Plus précisément :

```text
structure constitutive générale
≠ instance circulaire
≠ réalisation opérationnelle SAT
```

La circularité déploie et teste l’architecture constitutive ; elle n’est pas
présentée comme la définition générale de tous les rôles. L’instance SAT réalise
opérationnellement des états déjà constitués ; elle ne les constitue pas par
simple identification de types.

### 5.1 Créer une interface générique honnête

Le raccord générique doit maintenir deux relations distinctes :

```text
ConstitutiveState       = états constitués
ConstitutiveGenerator   = étapes qui produisent la constitution
ConstitutiveHistory     = histoires de ces étapes

OperationalRelation    = relations reconstruites après constitution
OperationalAction      = effet d’une relation découverte sur les continuations
```

Pour la couche fondatrice :

```text
ConstitutiveState     := PositiveConstitution P
ConstitutiveGenerator := GeneratedStep
```

Pour la couche opérationnelle, ne pas poser une égalité définitionnelle entre
`PositiveConstitution P` et l’état de recherche. Introduire une réalisation
construite :

```text
PositiveConstitution P
→ RealizedConstitutiveState
→ état opérationnel du SearchSystem
```

Cette réalisation doit fournir les correspondances exactes et les lois de
round-trip nécessaires. Elle réalise la constitution ; elle ne la remplace pas.

Cette identification ne doit fournir aucune conversion :

```text
GeneratedStep ≠ Transport
GeneratedStep → OperationalRelation
GeneratedStep → TransportCode
GeneratedStep → AcceptingContinuationTransport
```

Les trois flèches de ce bloc désignent précisément des conversions interdites :
aucune d’elles ne doit être introduite par construction.

Un `GeneratedStep` produit uniquement le nouvel état constitué et son histoire.
La recherche opérationnelle commence ensuite depuis cet état :

```text
GeneratedStep
→ nouvel état constitué / nouvelle histoire
→ extraction exécutable des candidats
→ discovery exécutable
→ Option OperationalRelation
→ construction éventuelle du code
→ validation
→ application
```

L’interface générique doit donc fournir séparément :

1. le producteur constitutif ;
2. l’extracteur de candidats sur un état constitué ;
3. le run de discovery retournant une relation optionnelle ;
4. l’action opérationnelle définie seulement pour une relation effectivement
   trouvée.

Une interface conditionnelle est acceptable à ce niveau, à condition d’être
clairement nommée comme interface. Elle ne doit jamais transformer la réussite
de la discovery en propriété définitionnelle de `GeneratedStep`.

### 5.2 Fermer ensuite l’instance concrète

Le théorème final ne devra pas laisser cette action sous forme d’hypothèse.

Il faudra construire une instance concrète reliant, par une réalisation puis
une exécution successives :

- les états engendrés ;
- leur réalisation exacte dans le système de recherche ;
- leurs continuations structurales ;
- leur acceptation ;
- l’extraction des candidats depuis l’état constitué ;
- la discovery locale optionnelle ;
- la relation locale lorsqu’elle est effectivement trouvée ;
- son action sur les continuations ;
- le résultat terminal.

L’action associée à une relation découverte devra porter sa propre preuve de
préservation de l’acceptation. Cette preuve ne découle ni de l’exactitude de la
réalisation, ni de l’existence d’un `GeneratedStep`.

Cette construction devra réutiliser les relations et actions déjà présentes,
notamment `generatedStructuralFlipAtAction`, plutôt que créer une seconde
sémantique parallèle.

La réussite locale sur la famille retenue devra être un théorème démontré à
partir des runs concrets. Elle ne devra pas être un champ automatique attaché à
toute étape constitutive.

### 5.3 Construire le chemin opérationnel depuis les discoveries exécutées

Définir par récursion un run de discovery le long de l’histoire effectivement
produite :

```lean
discoverGeneratedHistoryTransportPath
```

Il devra parcourir :

```text
History GeneratedStep source target
```

selon la chaîne suivante :

```text
état constitué k
→ extraction locale k
→ discovery locale k
→ Option relation k
→ si succès : atome de transport k
→ validation k
→ exécution k
→ état constitué suivant
```

La fonction générique doit pouvoir enregistrer un échec de discovery. La seule
existence d’une `History GeneratedStep` ne doit donc pas suffire à produire un
`ConstitutedPrimitivePath`.

Sur la famille concrète retenue, un théorème séparé établira que chaque discovery
locale réussit et que la liste des relations effectivement retournées forme un
chemin primitif exécutable.

Aucun témoin de relation ne devra être fourni extérieurement : les témoins du
chemin seront exactement ceux retournés par les runs de discovery.

### 5.4 Prouver les correspondances exactes

La construction structurelle doit être achevée avant toute mesure. L’histoire
est d’abord produite, les discoveries sont ensuite exécutées, puis le chemin et
le code sont construits depuis leurs résultats. Les égalités numériques
ci-dessous sont seulement des conséquences de ces objets déjà construits.

Pour toute profondeur `n` de la famille sur laquelle les discoveries sont
prouvées réussies :

```text
longueur de l’histoire générée = n + longueur du périmètre
nombre d’étapes ajoutées       = n
nombre de discoveries réussies = n
longueur du chemin primitif    = n
taille du code compilé         = n
requêtes de validation         = n
requêtes d’exécution           = n
candidats de composition       = 0
```

### 5.5 Préserver les identités constitutives

Chaque propriété doit faire l’objet d’un théorème de préservation distinct :

1. persistance des occurrences anciennes ;
2. distinction de l’occurrence fraîche ;
3. préservation de l’ordre des occurrences ;
4. préservation de la provenance ;
5. préservation de la différence résiduelle ;
6. préservation de l’acceptation par l’action opérationnelle ;
7. préservation de tout readout terminal effectivement revendiqué ;
8. naturalité sous changement de réalisation.

Les implications suivantes sont interdites sans preuve spécifique :

```text
transport exact
→ préservation automatique de l’acceptation
→ préservation automatique de la provenance
→ préservation automatique du readout
```

L’exactitude du transport établit les round-trips. Elle ne transporte aucune
propriété supplémentaire par elle-même.

### Critère de sortie

Sur l’instance concrète fermée, une histoire produite par
`iteratedHistory P n` doit pouvoir être parcourue, ses relations locales
découvertes, puis exécutées sans fournir séparément :

```text
sa liste de relations
sa liste de variables
son code
son endpoint
```

## 6. Phase IV — Imposer la succession opérationnelle

### But

Faire de la sortie de l’étape `k` l’entrée effective de l’étape `k + 1`.

### Travail

Construire un exécuteur récursif :

```lean
executeGeneratedHistory :
  initialContinuation
  → generatedHistory
  → GeneratedHistoryExecution
```

Pour chaque étape :

1. lire l’état courant produit ;
2. effectuer la discovery locale ;
3. examiner son résultat optionnel ;
4. construire la relation uniquement depuis le témoin retourné en cas de
   succès ;
5. construire et valider l’atome ;
6. appliquer l’atome à la continuation courante ;
7. utiliser la continuation retournée pour l’étape suivante.

La récursion ne doit jamais déduire la relation de la seule occurrence d’un
`GeneratedStep`. La réussite de chaque discovery sur la famille intégrée doit
être prouvée à partir du calcul effectué à cette étape.

Le type du run devra mémoriser :

```lean
stepInput (k + 1) = stepOutput k
```

### Théorèmes requis

```lean
execution.source = initialSource
execution.target = history.endpoint
execution.executedAtoms = generatedStepCount history
execution.compositionCandidates = 0
execution.terminalContinuation =
  foldOperationalSteps initialContinuation history
```

Un théorème de provenance devra relier chaque atome exécuté au run de discovery
effectué sur l’état constitué correspondant. L’occurrence de `GeneratedStep`
justifie la production de cet état, pas l’existence automatique de l’atome.

Les théorèmes de préservation devront rester séparés : identité de l’occurrence,
provenance, acceptation et valeur du readout terminal ne devront jamais être
concluses à partir de la seule exactitude d’un transport.

### Critère de sortie

Il ne doit exister aucun champ permettant de remplir directement le terminal
avec `history.endpoint`.

## 7. Phase V — Comptabilité complète et non inflatable

### But

Remplacer toute enveloppe déclarative par les statistiques du run canonique.

### 7.1 Compteurs de production

Compter pendant la récursion :

- appels à `generate` ;
- étapes ajoutées ;
- unités de provenance produites ;
- certificats produits.

### 7.2 Compteurs de discovery

Compter :

- clauses visitées ;
- littéraux visités ;
- candidats extraits ;
- candidats effectivement testés ;
- constructions et comparaisons de variables ;
- comparaisons de formules ;
- comparaisons d’histoires.

### 7.3 Compteurs d’exécution

Compter :

- atomes validés ;
- requêtes primitives ;
- atomes évalués ;
- applications aux continuations ;
- lectures terminales ;
- candidats de composition.

### 7.4 Total canonique

Définir le coût total depuis le run :

```lean
def ConstitutiveResolutionStats.total
    (stats : ConstitutiveResolutionStats) : Nat :=
  stats.production +
  stats.extraction +
  stats.discovery +
  stats.validation +
  stats.execution +
  stats.terminalReadout
```

Le coût ne doit pas être fourni par un témoin existentialement choisi.

### 7.5 Absence de double comptage

Prouver que :

- la production des certificats est chargée une fois ;
- leur lecture pendant la validation est une opération distincte ;
- leur application pendant l’exécution est une opération distincte ;
- aucune même récursion n’est additionnée deux fois sous deux noms.

### 7.6 Croissance

Prouver sur la famille intégrée :

```text
input₁ < input₂
→ profondeur(input₁) < profondeur(input₂)

input₁ < input₂
→ discoveryWork(input₁) < discoveryWork(input₂)
```

Puis établir la borne totale relativement à la taille réellement encodée de
l’entrée.

### Critère de sortie

Toute valeur de coût publiée doit être une projection du run effectivement
exécuté.

## 8. Phase VI — Théorème intégré de la relation constitutive

### But

Rassembler les résultats sans déclarer prématurément une clôture globale.

### 8.0 Rétroaction constitutive entre exécution et discovery suivante

La succession des affectations et la rétroaction constitutive sont deux
obligations différentes :

```text
sortie opérationnelle(k) = entrée opérationnelle(k + 1)
```

ne suffit pas à établir :

```text
les déterminations produites et transportées à l'étape k
participent aux données calculatoires depuis lesquelles sont construits
l'état opérationnel, les candidats et la discovery de l'étape k + 1.
```

La phase est fermée seulement si une récursion exécutée construit un état
transmis contenant l'affectation retournée, son lecteur instrumenté, les
décisions AND dans leur ordre, leur provenance et la constitution générale
produite. L'extraction, l'inspection des candidats et la discovery suivante
doivent consommer cet état. Une égalité ajoutée après coup, un champ mémorisé
mais jamais inspecté, ou un nouvel appel indépendant à
`stageRecordedDiscoveryRun depth` ne satisfont pas cette obligation.

Condition de sortie : deux états de même profondeur et de même projection,
mais portant des histoires de déterminations différentes positivement
construites, peuvent produire des outcomes de discovery suivante différents
avec le même moteur ; et l'histoire active est indexée par l'état constitué
complet retourné par l'étape précédente.

### Paquet de synthèse attendu

Le résultat final devra contenir au minimum :

```lean
structure ConstitutiveAndOrResolutionEvidence (input : Input) : Prop where
  generationIsEndogenous
  historyIsActuallyGenerated
  operationalRealizationIsExact
  discoveryIsEndogenous
  relationComesFromDiscovery
  codeComesFromRelation
  validationUsesProducedCode
  executionUsesValidatedCode
  terminalComesFromExecution
  decisionReadsTerminalOnly
  oldOccurrencesPersist
  freshOccurrenceRemainsDistinct
  provenancePersists
  acceptancePreservedByDiscoveredAction
  terminalReadoutPreserved
  realizationNaturality
  localExecutionIsExact
  measurementsAreDerived
  accountingIsExact
```

Puis un résultat familial :

```lean
structure ConstitutiveAndOrResolutionFamily : Prop where
  perInput :
    ∀ input, ConstitutiveAndOrResolutionEvidence input
  totalWorkBound :
    InputPolynomiallyBounded constitutiveResolutionProfile
  projectionCannotRecoverConstitution :
    ...
```

### Interprétation formelle

Le théorème devra établir simultanément :

```text
OR
= ouverture de plusieurs continuations possibles

AND
= accumulation des déterminations, contraintes et provenances
  qui constituent progressivement l’état courant

NP
= espace proof-relevant de continuations dans lequel
  la continuation acceptée n’est pas connue à l’avance

P
= capacité effective, dans l’état constitué courant,
  de découvrir, construire, valider et exécuter
  des relations/transports exploitables entre continuations
```

Le chemin n’est pas identifié à `P`. Le principe « le chemin est le calcul »
signifie que l’interaction des quatre rôles constitue progressivement le calcul :

```text
OR ouvre les possibles
→ AND constitue des déterminations
→ la constitution modifie l’état
→ l’état modifié change les relations reconstructibles
→ P reconstruit et exécute certaines de ces relations
→ la frontière est transformée
→ une nouvelle détermination devient possible
→ le cycle continue
```

La formulation intégrée finale est donc :

```text
OR produit l’ouverture structurelle des continuations possibles ;

AND accumule les déterminations, contraintes et provenances
qui constituent progressivement l’état courant ;

NP désigne le régime proof-relevant dans lequel plusieurs
continuations restent ouvertes sans que l’acceptée soit connue
à l’avance ;

P désigne la capacité effective, dans cet état constitué,
de découvrir, construire, valider et exécuter des relations
positives entre certaines continuations ;

NP AND/OR P désigne leur interaction constitutive dans la trajectoire :
les déterminations produites pendant le chemin modifient les relations
reconstructibles, et ces relations modifient à leur tour le calcul.
```

Le théorème ne devra pas reposer sur une équation nominale entre classes. Il
devra porter sur les constructions, les discoveries, les transports réellement
trouvés, leur exécution et leur coût.

## 9. Phase VII — Counterprobes obligatoires

Chaque attaque doit devenir une régression Lean.

### 9.1 Injection de la cible

Tentative : remplacer la cible produite par une cible externe.

Résultat exigé : impossibilité de construire le run typé.

### 9.2 Substitution de relation

Tentative : insérer une relation différente de celle retournée par la discovery.

Résultat exigé : incompatibilité d’indices ou contradiction avec l’égalité du
run.

### 9.3 Code non exécuté

Tentative : produire le terminal directement depuis la cible.

Résultat exigé : impossible via l’API publique ; le terminal exige un
`ExecutionResult`.

### 9.4 Variable présélectionnée

Tentative : construire le run public en fournissant la variable utile.

Résultat exigé : la procédure publique n’accepte aucun tel argument.

### 9.5 Discovery constante

Tentative : remplacer la discovery par un témoin subsingleton ou la réponse
connue.

Résultat exigé : les données attendues incluent le run d’extraction, les
candidats testés et leurs statistiques exactes.

### 9.6 Factorisation par l’entrée

Tentative : reconstruire le résultat depuis `input` et la projection.

Résultat exigé : contradiction fournie par les deux organisations de même entrée
et même projection.

### 9.7 Témoins sur instances disjointes

Tentative : utiliser une entrée pour le cas positif et une autre pour le cas
négatif.

Résultat exigé : le théorème intégré impose le même indice `input`.

### 9.8 Index spectateur

Tentative : montrer que tous les indices sont de simples renommages sans effet
opérationnel.

Résultat exigé : profondeur, histoire exécutée et statistiques varient avec
l’indice.

### 9.9 Compteurs constants

Tentative : maintenir `attempts = 1` ou des visites constantes quand l’entrée
grandit.

Résultat exigé : théorèmes de croissance stricte.

### 9.10 Coût inflatable

Tentative : ajouter arbitrairement un nombre au coût sans modifier le run.

Résultat exigé : le coût canonique est une fonction déterministe de la trace
d’exécution.

### 9.11 Clôture globale cachée

Tentative : exécuter une recherche globale à la place du chemin local.

Résultat exigé : le run certifie zéro candidat de composition.

### 9.12 Effacement de provenance

Tentative : remplacer deux histoires différentes par leur seule formule
terminale.

Résultat exigé : les projections coïncident, mais les exécutions restent
distinctes.

## 10. Phase VIII — Validation technique

### Pour chaque fichier Lean créé ou modifié

- preuve constructive ;
- aucun `sorry` ;
- aucun `axiom` ;
- aucun `noncomputable` ;
- aucune dépendance à `Classical`, `propext` ou `Quot.sound` ;
- exactement un bloc `AXIOM_AUDIT` en fin de fichier ;
- toutes les déclarations auditées existent ;
- aucun axiome affiché.

### Commandes de validation

```text
lake build
lake build AuditRegression
scripts/verify-manifest.sh
```

Puis scans complets :

```text
sorry
admit
axiom
noncomputable
unsafe
opaque
native_decide
implemented_by
```

### Vérifications scientifiques

- exécuter les runs positifs et négatifs sur plusieurs entrées ;
- vérifier la croissance des statistiques ;
- vérifier que les sorties proviennent du code évalué ;
- vérifier positivement la genèse et la provenance de chaque constitution avant
  de comparer leurs projections ;
- vérifier que le changement de provenance est la différence constitutive
  pertinente établie par la construction elle-même ;
- vérifier séparément la préservation de l’identité, de la provenance, de
  l’acceptation et du readout revendiqué ;
- vérifier que longueurs et coûts sont dérivés après construction des objets
  mesurés ;
- vérifier qu’aucune réponse attendue n’entre dans la signature publique.

## 11. Ordre strict d’implémentation

```text
1. Stabiliser OperationalProjectionInadequacy
2. Produire les deux constitutions depuis la même entrée
3. Établir positivement leur genèse, leur histoire et leur différence
4. Construire leur réalisation opérationnelle exacte
5. Intégrer extraction et discovery endogènes
6. Retirer selected, target et observed de l’API publique
7. Construire les relations uniquement depuis les discoveries réussies
8. Construire et appliquer les transports effectivement trouvés
9. Exécuter récursivement la succession stepOutput(k) → stepInput(k + 1)
10. Prouver séparément les propriétés effectivement préservées
11. Dériver les longueurs, tailles et coûts depuis les runs construits
12. Unifier la comptabilité et exclure le double comptage
13. Comparer les projections des deux constitutions déjà établies
14. Fermer le théorème même entrée / même projection / résultats différents
15. Déduire la non-factorisation opérationnelle
16. Construire le paquet de synthèse
17. Ajouter les counterprobes
18. Exécuter les audits constructifs et les builds
19. Lancer un audit adversarial indépendant
20. Corriger tout gap trouvé
21. Introduire un marqueur final uniquement après réussite de l’audit
```

## 12. Condition exacte d’achèvement

Le chantier sera achevé lorsque le dépôt contiendra une construction axiom-free
démontrant, sur une famille non bornée :

```text
l’état suivant est produit depuis l’état courant ;
sa réalisation opérationnelle est construite et exacte ;
la relation est découverte depuis les données produites ;
le code est construit depuis cette relation ;
le code est réellement appliqué ;
la continuation suivante est le résultat de cette application ;
le terminal est lu sur cette continuation ;
la décision dépend uniquement de ce terminal ;
chaque propriété préservée possède sa preuve spécifique ;
les longueurs et tailles sont dérivées après la construction ;
les coûts proviennent de l’exécution ;
le nombre d’étapes et le travail croissent avec l’entrée ;
l’exécution reste locale et sans explosion de clôture globale ;
deux constitutions sont produites et distinguées positivement ;
leurs projections sont ensuite démontrées égales ;
ces organisations de même entrée et de même projection
ont des comportements opérationnels différents lorsque leur
constitution/provenance diffère.
```

C’est ce raccord qui transformera les résultats actuellement séparés en une
démonstration intégrée de la relation constitutive `NP AND/OR P`.
