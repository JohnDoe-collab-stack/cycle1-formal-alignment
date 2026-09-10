# Plan temporaire — Architecture neuronale constitutive et alignement relatif

## 0. Statut et règle de suppression

Ce document est un plan interne d’exécution. Il ne constitue ni une preuve,
ni une spécification normative publiée, ni un résultat expérimental.

Il peut rester présent sur la branche de travail, mais doit être supprimé dans
la merge request ou pull request qui intègre le chantier dans `main`. S’il a été
commité sur la branche, sa suppression doit appartenir à cette même demande de
fusion : l’arbre résultant de `main` ne doit pas le contenir. Les décisions
scientifiques stabilisées devront être transférées dans les documents
canoniques et dans les types Lean correspondants ; l’historique de travail ne
doit pas devenir une dépendance du résultat.

État de reprise contrôlé :

- branche de travail : `codex/constitutive-transformer` ;
- dernier état gelé de la branche : commit `569701a` ; les corrections décrites
  ci-dessous appartiennent encore à l’arbre de travail non gelé ;
- les lots A à J ont produit un noyau fini compilé et une réalisation
  transformer à deux cycles liés ; la Gate K a été réouverte afin de reconstruire
  proprement la séparation entre apprentissage et évaluation ;
- l’itération uniforme sur une profondeur naturelle et la conservation d’une
  obligation sous itération sont déjà génériques dans `Succession.lean` ;
- la suite ne doit ni reconstruire ces acquis ni présenter les deux cycles finis
  comme une preuve déjà instanciée à toute profondeur ;
- les documents canoniques actuels sont
  `docs/fr/alignement_constitutif_transformers.md` et
  `docs/en/constitutive_transformer_alignment.md` ;
- l’ancien résultat confirmatoire ne satisfait pas la séparation désormais
  exigée et ne fait plus partie de l’état scientifique candidat à l’intégration.

## 1. Objectif final

Construire, dans ce dépôt et à partir de son noyau formel vérifié, une théorie
autonome de la machine neuronale constitutive qui :

1. individue ses objets par leur formation et leurs rôles relationnels ;
2. distingue constitution, réalisation, régime, norme et effectuation ;
3. définit une mémoire relative aux futurs pertinents ;
4. établit une dépendance causale entre apprentissage effectif, prédiction
   consommée, proposition constitutive modifiée et succession exacte ;
5. compose plusieurs transitions constitutives sans confondre apprentissage
   paramétrique, incorporation et succession de régime ;
6. traite une architecture transformer comme une réalisation particulière,
   et non comme la source de la constitution ;
7. localise constructivement les ruptures de fidélité, d’admission et de norme ;
8. conserve l’exactitude locale tout en respectant la non-clôture réflexive ;
9. possède une petite instance exécutable et falsifiable ;
10. possède une expérimentation neuronale sans oracle, réparation cachée ou
    audit causalement actif ;
11. instancie, pour toute profondeur finie, la dynamique transformer uniforme
    déjà disponible abstraitement ;
12. conserve un invariant gouverné sur tous les états atteignables, en séparant
    les mises à jour de paramètres, de mémoire, de régime et de norme ;
13. établit une frontière de raffinement explicite entre la trace exécutable et
    les objets formels, sans transformer une observation numérique en preuve.

Le résultat final doit être compréhensible, compilable et vérifiable depuis ce
dépôt seul.

## 2. Autorité scientifique du dépôt

### 2.1 Résultats déjà disponibles

Le chantier part exclusivement des objets présents ici :

- `History` et `History.Occurrence` ;
- les rôles internes et résiduels ;
- les réalisations exactes et fidèles ;
- `RegimeExit` et `UniformRegimeExit` ;
- `RootedGeneratedHistory` ;
- `NormativeAdequacy` et `AdequateAlong` ;
- `CircularRefinement` ;
- `CircularSpecificationSatisfaction` ;
- les transformations de soundness et de complétude ;
- `oneStepAfterPerimeter` et sa sortie relative à la spécification ;
- `Represents`, `InternallyRepresentable` et `diagonalStatus` ;
- le transport représentationnel de l’adéquation ;
- la non-clôture réflexive globale.

### 2.2 Discipline des revendications

Chaque énoncé du futur document devra recevoir exactement l’un des statuts :

| Statut | Signification |
| --- | --- |
| démontré | théorème compilé dans ce dépôt et inclus dans l’audit axiomatique |
| défini | structure ou notion formellement définie, sans théorème supplémentaire implicite |
| dérivé architecturalement | conséquence de conception argumentée depuis les résultats formels |
| spécifié | contrat à satisfaire par une réalisation future |
| implémenté | code exécutable présent et testé, sans promotion automatique au rang de preuve |
| observé | résultat d’un protocole expérimental gelé et reproductible |
| ouvert | obligation non encore satisfaite |

Aucune formulation ne doit convertir un résultat spécifié, implémenté ou
observé en théorème.

### 2.3 État de fermeture à la reprise

La table suivante est l’autorité de pilotage pour la suite. Le futur employé
dans les lots A à M enregistre leurs obligations initiales ; il ne signifie pas
qu’elles sont encore toutes ouvertes.

| Lot | État actuel du chantier | Portée exacte |
| --- | --- | --- |
| A | fermé | documents français et anglais stabilisés et raccordés aux identifiants Lean |
| B | fermé | machine constitutive abstraite et ponts avec le Cycle 1 |
| C | fermé dans la portée déclarée | mémoire exacte relative à une famille explicite de futurs et mise à jour autonome finie |
| D | fermé | admission, norme autonome, certificat indexé et effectuation gouvernée |
| E | fermé au niveau générique | itération uniforme sur `Nat`, histoire produite et conservation d’une obligation sous itération |
| F | fermé | transport représentationnel et non-clôture réflexive distincte de la sortie opérationnelle |
| G | fermé | modèle de référence fini, causalité parent–appris et deux cycles liés |
| H | fermé | contrat neuronal, vue autorisée, trajectoire fidèle et audit différé |
| I | fermé dans l’instance finie | transformer booléen à attention dure, intervention, sonde fraîche fixée et anti-substitution, contrôle inerte et renommage |
| J | fermé pour deux cycles | lien intercycle, ablation, mémoire d’attention, hallucination relative et confinement |
| K | réouvert jusqu’au nouveau gel | le protocole canonique unique sépare entraînement, sonde de smoke test et sonde confirmatoire non exécutée ; le run confirmatoire doit attendre le commit de gel |
| L | fermé dans l’instance finie | atteignabilité proof-relevant, invariant gouverné, transformations admissibles et dynamique uniforme pour tout `n : Nat` |
| M | partie Lean fermée, contrôle exécutable à régénérer | raffinement formel exact et séparateurs construits ; vérificateur à resceller sur l’unique résultat corrigé |

Les quatre obligations formelles qui formaient le chemin critique sont fermées
dans leur portée déclarée :

1. instancier à profondeur finie arbitraire la dynamique transformer, et non la
   seule transition abstraite ;
2. agréger mémoire, adéquation et effectuation dans un invariant préservé sur
   tous les états atteignables ;
3. définir les transformations admissibles de la machine et transporter
   explicitement l’adéquation ;
4. raffiner la frontière exécutable vers le noyau formel.

Le travail restant concerne le gel du protocole corrigé, son run confirmatoire
unique, le rescellement du vérificateur, la synchronisation de la documentation
et de l’audit, puis l’intégration contrôlée dans `main`. La Gate L et la partie
Lean de la Gate M restent fermées.

## 3. Invariants non négociables

### 3.1 Constructivité

Tout nouveau fichier Lean doit :

- être sans `axiom`, `sorry` ou trou de preuve ;
- éviter `Classical`, `propext` et `Quot.sound` ;
- construire positivement les témoins utilisés ;
- contenir exactement un bloc `AXIOM_AUDIT` à la fin ;
- compiler avec le toolchain figé du dépôt.

### 3.2 Non-substitution

Une réalisation neuronale peut proposer, approximer et transporter. Elle ne
peut pas :

- définir rétroactivement l’identité de l’objet ;
- produire un certificat en copiant le résultat attendu ;
- remplacer un candidat invalide par le candidat correct ;
- consulter une décision normative future ;
- utiliser l’audit pour choisir la trajectoire ;
- masquer une rupture en supprimant sa trace.

### 3.3 Séparations obligatoires

Les distinctions suivantes doivent rester visibles dans les types :

```text
construction          ≠ réalisation
réalisation           ≠ admission
admission             ≠ satisfaction normative
norme                 ≠ adéquation du régime
proposition           ≠ incorporation
apprentissage         ≠ succession constitutive
composition en trace  ≠ dépendance causale
causalité à un pas    ≠ autonomie multicycle
sortie opérationnelle ≠ sortie représentationnelle
OOD structurel        ≠ diagonalisation réflexive
diagnostic            ≠ prévention de l’effectuation
```

### 3.4 Autonomie documentaire et technique

- Aucun fichier requis ne doit être situé hors du dépôt.
- Aucun lien extérieur ne doit porter une définition, une preuve ou une
  condition de reproduction ; une citation éventuelle ne peut fournir que du
  contexte.
- Aucune preuve ne doit dépendre d’un artefact non inventorié.
- Toute information nécessaire à la reproduction doit être locale et versionnée.

## 4. Protocole de transplantation contrôlée

### 4.1 Principe

Le chantier peut réemployer un matériau de recherche antérieur, y compris une
définition, une structure de preuve, un modèle fini ou un fragment de protocole.
Ce réemploi n’autorise ni l’importation d’un second cadre, ni la création d’une
dépendance scientifique extérieure.

La règle est :

```text
repérage interne
→ extraction hors du dépôt
→ isolation des dépendances
→ traduction dans le vocabulaire canonique local
→ reconstruction dans les interfaces locales
→ compilation et tests séparateurs
→ intégration du seul résultat autonome
```

La copie brute est donc permise uniquement dans un espace temporaire extérieur
au dépôt. Elle sert à éviter de perdre une construction utile pendant son
analyse. Aucun fragment brut, chemin source, historique source ou nom de projet
source ne doit entrer dans les fichiers suivis par Git.

### 4.2 Critères d’éligibilité

Un fragment peut être retenu s’il satisfait toutes les conditions suivantes :

- il répond à une obligation explicite d’un lot du présent plan ;
- son contenu mathématique ou algorithmique peut être énoncé indépendamment de
  son contexte d’origine ;
- ses entrées, sorties et hypothèses peuvent être rendues visibles ;
- il se raccorde à une interface locale sans modifier rétroactivement le noyau ;
- il n’exige ni oracle, ni cible cachée, ni réparation du candidat ;
- il peut recevoir un test positif et au moins un test séparateur négatif ;
- son statut final peut être classé sans ambiguïté comme défini, démontré,
  implémenté, observé ou ouvert ;
- son droit de réemploi est établi ; tout contenu tiers ou de statut incertain
  est exclu jusqu’à clarification.

Sont prioritaires les fragments courts portant une seule responsabilité :

- contrats de mémoire relative aux futurs ;
- structures de succession constitutive ;
- actions typées, certificats et effectuation ;
- séparation des plans de réalisation ;
- modèles finis non triviaux ;
- tests de fuite, d’oracle, de réparation et d’audit actif.

### 4.3 Critères de rejet

Un fragment est rejeté, même s’il fonctionne dans son ancien contexte, lorsqu’il :

- importe un graphe de dépendances disproportionné ;
- duplique un objet déjà canonique dans ce dépôt ;
- impose un vocabulaire concurrent impossible à traduire exactement ;
- confond formation, réalisation, régime, norme ou effectuation ;
- dépend d’une constante, d’une fixture ou d’un résultat attendu caché ;
- juxtapose apprentissage et proposition dans une même trace sans démontrer que
  la prédiction apprise est effectivement consommée par la proposition ;
- n’est correct que pour un catalogue fini choisi après les résultats ;
- répare, remplace ou efface les candidats invalides ;
- transforme une observation empirique en garantie formelle ;
- introduit un axiome, un principe interdit ou un trou de preuve ;
- ne peut pas être testé indépendamment après isolation.

Le rejet d’un fragment n’est pas le rejet de l’idée qu’il tentait d’exprimer.
L’idée peut être reconstruite directement depuis les fondements locaux.

### 4.4 Registre temporaire de décision

Chaque fragment examiné reçoit un identifiant interne neutre et une fiche
temporaire contenant :

```text
identifiant
obligation locale visée
contenu conceptuel retenu
dépendances détectées
contenu rejeté
interface locale cible
tests exigés
verdict : REJET / RÉÉCRITURE / TRANSPLANTATION MINIMALE
```

Ce registre ne contient aucun chemin ou nom extérieur. Il reste non suivi par
Git et doit être supprimé avec les espaces d’extraction avant le dernier commit.
Les décisions durables sont réénoncées dans les documents et types canoniques ;
le registre lui-même n’est ni une source scientifique ni une pièce de preuve.

### 4.5 Modes d’intégration

Trois verdicts seulement sont admis :

1. `REJET` : le fragment ne fournit rien qui satisfasse les critères ;
2. `RÉÉCRITURE` : seule l’idée ou la forme du contrat est conservée, puis le
   contenu est reconstruit depuis les types locaux ;
3. `TRANSPLANTATION MINIMALE` : un fragment autonome est repris à portée
   réduite, renommé, raccordé puis prouvé dans ce dépôt.

La réécriture est le mode par défaut. La transplantation minimale doit être
justifiée par une réduction réelle du risque ou du travail, jamais par la seule
existence du fragment.

### 4.6 Gate T — Admission d’un fragment

Avant l’intégration d’un fragment, vérifier :

- une seule interface locale cible est nommée ;
- toutes les dépendances ont été remplacées par des imports du dépôt ou par des
  définitions locales nécessaires ;
- aucun identifiant, commentaire, lien ou chemin extérieur ne subsiste ;
- les hypothèses et la portée de validité sont explicites ;
- le fragment compile isolément dans son module de destination ;
- les tests positifs et séparateurs passent ;
- l’audit axiomatique est vide ;
- l’intégration ne modifie pas les théorèmes déjà publiés ;
- le diff Git ne contient que la reconstruction admise.

L’échec d’un seul point renvoie le fragment en réécriture ou au rejet. La Gate T
ne remplace pas la gate du lot destinataire : les deux doivent être fermées.

### 4.7 Routage initial

Le premier inventaire sera limité aux familles suivantes :

| Famille examinée | Destination locale | Lot | Mode présumé |
| --- | --- | --- | --- |
| mémoire relative aux futurs | `CausalMemory.lean` | C | réécriture |
| action, certificat, effet | `NormativeExecution.lean` | D | réécriture |
| diagnostics génériques de rupture | `NormativeFailure.lean` | D | réécriture |
| cycle et succession | `Succession.lean` | E | réécriture |
| apprentissage causant la proposition suivante | `LearningCausality.lean` | E | réécriture prioritaire |
| exemples finis séparateurs | `ReferenceModel.lean` | G | transplantation minimale possible |
| séparation des plans neuronaux | `NeuralRealization.lean` | H | réécriture |
| causalité d’une structure proposée | `TransformerRealization.lean` | I | réécriture |
| tests anti-oracle et audit différé | protocole exécutable | K | transplantation minimale possible |

Ce tableau n’accorde aucune admission anticipée. Il indique seulement où
examiner le matériau ; la Gate T décide fragment par fragment.

## 5. Architecture cible

La dépendance conceptuelle canonique sera :

```text
fondements structurels
        ↓
alignement relatif
        ├────────────────→ non-clôture réflexive
        ↓
machine constitutive abstraite
        ↓
mémoire causalement fidèle
        ↓
admission et effectuation normatives
        ↓
succession constitutive
        ↓
contrat causal apprentissage → prédiction consommée
                → proposition → succession
        ↓
modèle fini : témoin causal à un pas et deux cycles liés
        ↓
réalisation neuronale abstraite
        ↓
réalisation transformer finie : causalité et deux cycles liés
        ↓
itération transformer à profondeur finie arbitraire
        ↓
invariant gouverné sur les états atteignables
        ↓
transformations admissibles et transport de l’adéquation
        ↓
raffinement de la frontière exécutable
        ↓
diagnostics conservés : mémoire, horizon, rupture normative
```

Le noyau existant ne sera pas réécrit pour s’adapter à l’application. Les
nouveaux modules importeront ses interfaces et construiront les ponts requis.

## 6. Arborescence formelle prévue

```text
ConstitutiveAlignment.lean
ConstitutiveAlignment/
  Machine.lean
  CausalMemory.lean
  NormativeExecution.lean
  NormativeFailure.lean
  Succession.lean
  LearningCausality.lean
  ReflectiveMachine.lean
  ReferenceModel.lean
  NeuralRealization.lean
  TransformerRealization.lean
  TransformerDynamics.lean
  GovernedDynamics.lean       -- extension prévue
  ExecutableRefinement.lean   -- extension prévue
```

La façade `ConstitutiveAlignment.lean` importe les modules présents dans leur
ordre de dépendance. Les extensions prévues ne lui seront ajoutées, ainsi qu’à
`lakefile.toml`, qu’après leur compilation indépendante.

### 6.1 Colonne vertébrale existante

Le graphe d’imports déjà vérifié est :

```text
Init
  ↓
SegmentedResidualRole.lean
  ↓
AbstractSegmentedTurning.lean
  ↓
StrongPerimetralTurning.lean

Init
  ↓
Cycle2/DiagonalizationKernel.lean

StrongPerimetralTurning.lean
        +
Cycle2/DiagonalizationKernel.lean
        ↓
Cycle2/ReflectiveAlignment.lean
```

Cette colonne vertébrale reste inchangée. Les nouveaux modules se placent
au-dessus d’elle ; aucun résultat du Cycle 1 ne doit être recopié sous une autre
forme pour fabriquer artificiellement une nouvelle fondation.

### 6.2 Responsabilité de chaque fichier existant

| Fichier | Autorité réutilisée dans la nouvelle architecture |
| --- | --- |
| `SegmentedResidualRole.lean` | rôles internes et résiduels, réalisation exacte, non-réutilisation et unicité de l’occurrence résiduelle |
| `AbstractSegmentedTurning.lean` | frontière abstraite, régime obstrué, `RegimeExit`, `UniformRegimeExit` et transport par réalisation fidèle |
| `StrongPerimetralTurning.lean` | histoires proof-relevant, occurrences, formation, provenance, réalisations fidèles, génération, norme autonome, adéquation, soundness, complétude et sortie opérationnelle concrète |
| `Cycle2/DiagonalizationKernel.lean` | représentation, statut diagonal, sortie représentationnelle et non-clôture globale abstraite |
| `Cycle2/ReflectiveAlignment.lean` | statuts du régime et de la norme, transport de leur adéquation et coexistence entre exactitude déterminée et non-clôture globale |

Les contrats nouveaux de mémoire, d’effectuation, de succession et de
réalisation neuronale ne sont pas déclarés déjà prouvés par ces fichiers. Ils
devront être construits dans leurs propres modules, puis composés avec les
résultats ci-dessus.

### 6.3 Graphe d’imports cible

Chaque module importe la dépendance la plus faible qui fournisse réellement ses
objets. Le graphe cible est :

```text
StrongPerimetralTurning
        ↓
ConstitutiveAlignment.Machine
        ├───────────────┐
        ↓               ↓
    CausalMemory   NormativeExecution
        └───────┬───────┘
                ↓
           Succession
                ↓
       LearningCausality

Machine + NormativeExecution
                ↓
        NormativeFailure

NormativeExecution + Cycle2.ReflectiveAlignment
                ↓
        ReflectiveMachine

LearningCausality + ReflectiveMachine + NormativeFailure
                ├────────────────────┐
                ↓                    ↓
       ReferenceModel       NeuralRealization
                                     ↓
                            TransformerRealization

ReferenceModel + TransformerRealization + Succession
                ↓
                            TransformerDynamics

TransformerDynamics + NormativeExecution + CausalMemory
                ↓
                            GovernedDynamics

GovernedDynamics + NeuralRealization
                ↓
                            ExecutableRefinement

ReferenceModel + TransformerDynamics + GovernedDynamics
               + ExecutableRefinement
                ↓
      ConstitutiveAlignment
```

Le graphe exact pourra être encore aminci pendant la compilation, mais jamais
épaissi par commodité. La façade racine importe les feuilles ; aucune feuille ne
doit importer la façade racine.

### 6.4 Théorèmes de pont obligatoires

Les noms définitifs seront choisis à la compilation, mais les obligations sont
fixes :

1. construire une instance de `ConstitutiveMachine` depuis une présentation et
   ses histoires du Cycle 1 sans redéfinir `History.Occurrence` ;
2. transporter l’individuation et la distinction des rôles depuis une
   réalisation fidèle du Cycle 1 vers l’interface machine ;
3. relever `RegimeExit` et `UniformRegimeExit` dans les diagnostics de la
   machine sans convertir la sortie en échec normatif ;
4. transporter `NormativeAdequacy` et `AdequateAlong` vers l’interface
   d’admission sans définir la norme depuis le régime ;
5. exposer séparément les deux transformations entre `CircularRefinement` et
   `CircularSpecificationSatisfaction`, puis leur équivalence propositionnelle
   au niveau de `Nonempty` ;
6. projeter `oneStepAfterPerimeter` comme témoin de sortie opérationnelle et
   conserver la réfutation de la satisfaction normative correspondante ;
7. raccorder les statuts déterminés de la machine à `PullbackStatus` et
   `transportRepresentation` ;
8. transporter `diagonalStatus_notRepresentable` et
   `noGlobalReflectiveClosure` vers une sortie représentationnelle explicitement
   distincte de la sortie opérationnelle ;
9. fournir un théorème de composition conditionnel : toute réalisation
   neuronale ou transformer qui satisfait le contrat de fidélité hérite des
   garanties structurelles correspondantes, sans prétendre que le réseau produit
   lui-même les preuves ;
10. construire un contrat causal séparant strictement l’état parent et l’état
    appris, puis montrer qu’une prédiction modifiée et effectivement consommée
    produit une proposition constitutive différente et une succession exacte ;
11. fermer, sur le modèle de référence fini, au moins une chaîne complète allant
    d’une occurrence du Cycle 1 à son transport opérationnel, son admission et
    son diagnostic final ;
12. instancier `iterateState`, `iterateHistory` et
    `preservesAlongIteration` avec l’opérateur transformer, pour toute profondeur
    `n : Nat`, sans catalogue de cycles ;
13. définir une famille proof-relevant d’états atteignables et montrer qu’un
    invariant réunissant mémoire, adéquation, fidélité de la trace et
    effectuation certifiée est préservé à chaque transition puis à toute
    profondeur finie ;
14. définir une transformation admissible entre deux machines indexées, avec
    transports explicites du régime, de la norme, de la mémoire et des
    certificats, puis construire l’adéquation cible depuis l’adéquation source ;
15. définir la relation de raffinement entre une trace exécutable scellée et la
    trace formelle effectivement consommée, sans demander au producteur neuronal
    de fabriquer un témoin Lean.

Un théorème de pont ne doit pas être un simple renommage d’un champ supposé. Il
doit soit construire le témoin cible, soit composer explicitement des témoins
déjà construits.

### 6.5 Frontière des garanties

| Revendication | Ancrage | Statut attendu |
| --- | --- | --- |
| individuation par formation et rôle | Cycle 1 | déjà démontré, puis transporté |
| sortie opérationnelle relative | Cycle 1 | déjà démontrée, puis projetée |
| adéquation exacte régime–norme | Cycle 1 | définie génériquement et démontrée sur l’instance circulaire ; exigée ailleurs comme contrat explicite |
| exactitude déterminée sans clôture globale | Cycle 2 | déjà démontrée, puis instanciée pour la machine |
| mémoire relative aux futurs | `CausalMemory.lean` | démontrée dans la portée déclarée et instanciée sur les modèles finis |
| effectuation gouvernée | `NormativeExecution.lean` | démontrée sous certificat et adéquation, puis instanciée |
| succession constitutive | `Succession.lean` | itération uniforme et conservation générique démontrées pour tout `n : Nat` |
| apprentissage causant la proposition suivante | lots E, G et I | contrat générique et instances finies démontrés |
| autonomie multicycle finie | lots G, J et L | deux cycles explicités puis même dynamique transformer construite pour tout `n : Nat` |
| réalisation neuronale fidèle | `NeuralRealization.lean` | contrat formel et instance finie construits |
| réalisation transformer | `TransformerRealization.lean` et `TransformerDynamics.lean` | instance finie construite et testée ; aucune garantie automatique issue du Cycle 1 |
| invariant gouverné atteignable | `GovernedDynamics.lean` | démontré sur l’instance finie pour tout `n : Nat` par préservation à un pas et itération existante |
| transformation admissible | `GovernedDynamics.lean` | contrats séparés et transports explicites de l’adéquation, de l’exécution, des actions et certificats |
| raffinement exécutable–formel | `ExecutableRefinement.lean` puis vérificateur à resceller | relation formelle exacte sur la frontière discrète ; contrôle exécutable à produire après le run confirmatoire gelé, sans formaliser les flottants |
| comportement empirique | protocole canonique unique | smoke test frais réussi ; résultat confirmatoire à régénérer seulement après commit du protocole corrigé |

Cette table doit être reprise dans les deux documents canoniques. Elle empêche à
la fois de détacher l’application du Cycle 1 et d’attribuer au Cycle 1 des
résultats neuronaux qu’il ne contient pas.

### 6.6 Gate de raccordement Cycle 1–application

Avant de déclarer un nouveau module relié au noyau :

- son chemin d’import jusqu’au fichier d’autorité est explicite ;
- chaque objet réutilisé garde son type source ou possède une conversion prouvée ;
- chaque conversion possède ses lois d’aller-retour ou sa propriété de fidélité
  adaptée ;
- les sorties opérationnelle, normative et représentationnelle restent dans des
  types distincts ;
- les théorèmes de pont figurent dans l’`AXIOM_AUDIT` du module ;
- un test séparateur échoue si le pont est remplacé par une projection constante ;
- la documentation cite l’identifiant Lean exact du pont ;
- la chaîne d’imports est acyclique et vérifiée par `lake build`.

Cette gate s’applique en plus de la Gate T lorsqu’un fragment transplanté est
utilisé pour construire le raccordement.

## 7. Lot A — Stabilisation conceptuelle française

### A1. Recentrer le titre et la thèse

Le document ne doit plus prendre le transformer comme objet fondamental. La
machine constitutive est l’architecture ; le transformer en est une réalisation
neuronale possible.

Titre de travail :

> **Architecture neuronale constitutive pour l’alignement relatif**
>
> *Mémoire causale, succession et réalisation par transformer*

### A2. Réorganiser le document

Ordre requis :

1. résultats formels de départ ;
2. conséquence architecturale de la non-clôture ;
3. machine constitutive abstraite ;
4. séparation des quatre plans de réalisation et des cinq distinctions
   constitutives ;
5. mémoire relative aux futurs ;
6. succession constitutive ;
7. causalité de l’apprentissage vers la proposition suivante à un pas ;
8. itération générique déjà démontrée, instance transformer à deux cycles et
   généralisation transformer maintenue comme obligation ouverte ;
9. réalisation neuronale ;
10. instance transformer ;
11. rupture normative et hallucination ;
12. programme formel ;
13. programme d’implémentation ;
14. statut exact.

### A3. Corriger les revendications

- Employer « diagnostic et confinement normatifs » : le théorème
  d’effectuation gouvernée est construit, mais il ne prouve ni la suppression de
  la génération interne ni l’absence générale d’hallucinations linguistiques.
- Ne pas présenter la mémoire comme conservation intégrale de l’histoire.
- Ne pas présenter toute sortie hors régime comme une hallucination.
- Ne pas présenter le transformer comme détenteur des témoins Lean.
- Ne pas identifier non-clôture réflexive et OOD structurel.
- Ne pas présenter une composition ou une trace commune comme une dépendance
  causale de l’apprentissage vers la proposition.
- Ne pas présenter la causalité à un pas comme une autonomie multicycle déjà
  obtenue.

### Gate A

- document français autonome et cohérent ;
- chaque affirmation classée par statut ;
- aucune référence absente ;
- aucune anticipation de théorème ;
- accord explicite entre le plan documentaire et l’ordre formel.

## 8. Lot B — Machine constitutive abstraite

### B1. Structure minimale

Construire une interface paramétrée par :

```lean
State : Type
Step : State → State → Type
```

et réutiliser l’histoire proof-relevant existante. La machine devra fournir ou
indexer :

- ses histoires exécutables ;
- les occurrences formées dans ces histoires ;
- les continuations candidates ;
- leur réalisation fidèle ;
- le régime opérationnel ;
- la norme autonome ;
- l’adéquation du régime à la norme.

### B2. Pas confondre structure et instance

`ConstitutiveMachine` ne doit contenir aucune hypothèse transformer, token,
vecteur, attention ou réseau. Il doit rester instanciable par un modèle fini
non neuronal.

### B3. Théorèmes cibles

- transport d’une occurrence le long d’une réalisation fidèle ;
- conservation de l’individuation sous composition de réalisations ;
- impossibilité de fusionner deux rôles distincts sous réalisation injective ;
- projection d’une sortie relative existante vers l’interface machine ;
- absence de conclusion normative sans `NormativeAdequacy`.

### Tests séparateurs

- carrier unitaire incapable de distinguer deux rôles requis ;
- même lecture pour deux occurrences de formations différentes ;
- réalisation terminalement correcte mais non fidèle à la trajectoire ;
- régime et norme extensionnellement différents.

### Gate B

- module compilé constructivement ;
- instance circulaire construite depuis les objets existants ;
- au moins un modèle séparateur empêchant chaque confusion principale ;
- aucune modification substantielle du noyau Cycle 1.

## 9. Lot C — Mémoire relative aux futurs pertinents

### C1. Questions et comportements

Définir constructivement :

```lean
Question
Answer : Question → Type
behaviour : State → (q : Question) → Answer q
```

Puis :

```lean
FutureEquivalent left right :=
  ∀ q, behaviour left q = behaviour right q
```

La première version emploiera une famille de questions explicitement donnée.
Elle ne prétendra pas quantifier sur toutes les questions concevables.

### C2. Contrats de mémoire

Définir :

```text
solidité causale
  même mémoire → mêmes futurs pertinents

complétude relative
  mêmes futurs pertinents → même mémoire

exactitude relative
  même mémoire ↔ mêmes futurs pertinents
```

Éviter un quotient Lean primitif si son usage exige des principes non permis.
La première formalisation doit préférer une interface d’encodage et ses deux
lois explicites.

### C3. Mise à jour autonome

Pour une transition `advance`, construire une mise à jour `update` et la loi :

```text
encode (advance state) = update (encode state)
```

La mémoire devient alors une capitalisation utilisable, pas seulement une
classification postérieure des histoires.

### C4. Contraction sûre

Prouver seulement :

```text
fusion par la mémoire
→ indistinction sous les questions déclarées
```

La contraction irréversible sous tout enrichissement futur restera ouverte
tant qu’une stabilité correspondante n’est pas démontrée.

### Tests séparateurs

- deux états de même lecture présente mais de futurs différents ;
- famille de questions trop pauvre fusionnant deux états ;
- enrichissement de la famille révélant une ancienne différence ;
- mémoire injective conservant toute l’histoire, solide mais non minimale ;
- mise à jour ne commutant pas avec la transition réelle.

### Gate C

- notions de solidité, complétude et exactitude séparées ;
- théorème de non-fusion pour une différence future ;
- loi de mise à jour sur une instance finie ;
- aucune revendication de mémoire universellement minimale.

## 10. Lot D — Admission, norme et effectuation

### D1. Action canonique

Définir une action avant son effet, avec au minimum :

- sa nature ;
- sa cible ;
- ses paramètres ;
- son contexte constitutif ;
- sa portée ;
- l’effecteur demandé.

### D2. Certificat d’autorisation

Un certificat doit être indexé par l’action exacte et le contexte exact. Il ne
doit pas autoriser une action voisine par simple conversion nominale.

### D3. Loi d’effectuation

Construire une interface dans laquelle un effet ne peut être produit qu’à
partir d’un certificat valide :

```text
effectuation(action, context)
→ admission(action, context)
```

Puis composer avec la soundness normative :

```text
effectuation
→ admission
→ satisfaction de la norme
```

### D4. Non-interférence

La décision d’admission ne doit pas modifier le candidat, sa constitution ou
sa mesure afin de fabriquer sa conformité.

### D5. Diagnostics génériques en amont

Définir dans `NormativeFailure.lean`, sans dépendance neuronale :

```text
FormationFailure
RegimeExit          -- réutilisé, jamais redéfini
NormativeFailure
```

`FormationFailure` localise l’échec d’élaboration d’un candidat. `RegimeExit`
conserve exactement son sens structurel existant. `NormativeFailure` porte un
candidat formé et réalisé dont la norme autonome est réfutée. Ces trois types ne
doivent être ni convertibles par défaut ni regroupés dans un booléen unique.

### Tests séparateurs

- certificat pour une autre cible ;
- certificat expiré ou consommé deux fois ;
- action modifiée après admission ;
- candidat rejeté mais rendu effectif par une voie non médiée ;
- norme définie à partir de la décision du régime.

### Gate D

- effet impossible sans certificat dans l’interface formelle ;
- théorème `effectuation → norme` sous adéquation ;
- distinction entre rejet du candidat et impossibilité de l’effectuer ;
- diagnostics génériques définis avant toute instance neuronale ;
- modèle négatif montrant qu’une voie non médiée invalide la garantie.

## 11. Lot E — Succession constitutive et raisonnement long

### E1. Trois transitions

Formaliser séparément :

```text
apprentissage paramétrique : paramètres → paramètres
incorporation constitutive : état → état étendu
succession normative       : régime → régime successeur
```

### E2. Cycle constitutif

Un cycle doit consommer un état réellement produit et construire :

- un candidat ;
- sa réalisation ;
- son diagnostic de régime et de norme ;
- une conséquence autorisée ;
- une incorporation éventuelle ;
- un état successeur ;
- le régime successeur correspondant.

L’état successeur ne doit pas être fourni comme une donnée libre choisie après
le candidat.

### E3. Causalité constitutive de l’apprentissage à un pas

Construire dans `LearningCausality.lean` un contrat portant explicitement :

```text
état prédictif parent
→ apprentissage effectif
→ état prédictif appris
→ prédictions parent et apprise
→ prédictions effectivement consommées comme entrées constitutives
→ propositions constitutives correspondantes
→ verdicts de succession correspondants
```

Le témoin causal compare deux parcours dont le problème, l’état constitutif, le
producteur de proposition et son aléa sont identiques. La seule variation
initiale autorisée est l’état prédictif parent ou appris. Le contrat exige :

- une prédiction parent différente de la prédiction apprise ;
- l’identité entre chaque prédiction et l’entrée réellement consommée par le
  producteur constitutif ;
- deux propositions constitutives différentes ;
- un motif de rejet précis pour la branche parent ;
- une succession exacte construite pour la branche apprise ;
- un cas d’intervention fixé avant l’observation des résultats ;
- une reconstruction déterministe du témoin complet.

La présence de l’apprentissage et de la proposition dans une même trace ne
satisfait aucune de ces obligations. Ce résultat à un pas ne vaut pas non plus
comme preuve d’autonomie multicycle.

### E4. Itération générique — fermée

`Succession.lean` définit déjà `iterateState` et `iterateHistory` pour toute
profondeur `n : Nat`. Le même `UniformTransition` consomme littéralement la
sortie du cycle précédent ; aucun `cycle0`, `cycle1` ni catalogue par profondeur
n’intervient dans cette définition.

Ce résultat ferme l’itération abstraite. `TransformerDynamics.lean` construit
deux cycles causalement liés, puis `GovernedDynamics.lean` instancie le même
opérateur à toute profondeur finie et ferme la généralisation concrète du lot L.

### E5. Conservation générique et agrégation — fermées

L’horizon est défini par composition de transitions constituées, non par nombre
de tokens. `preservesAlongIteration` prouve déjà qu’une obligation préservée à
un pas reste satisfaite après toute profondeur finie.

`GovernedDynamics.lean` forme ensuite l’obligation agrégée propre à la machine
gouvernée — mémoire, adéquation, fidélité, statut normatif, conservation de
l’élaboration et confinement — et fournit sa loi constructive de préservation à
un pas. Le théorème `invariantAt` la transporte à tout `n : Nat` par l’itération
existante.

### Tests séparateurs

- plusieurs reconstructions mathématiques indépendantes présentées à tort
  comme une itération ;
- second cycle consommant une fixture plutôt que le premier état produit ;
- même état terminal obtenu par une trajectoire infidèle ;
- apprentissage des poids sans incorporation ;
- incorporation sans acquisition ni rétention ;
- apprentissage et proposition seulement juxtaposés dans une trace ;
- proposition indépendante de la prédiction apprise ;
- contexte constitutif modifié en même temps que l’état prédictif ;
- cas causal choisi après observation du succès ;
- deuxième cycle alimenté par une donnée correcte fournie séparément.

### Gate E

- contrat causal à un pas compilé dans `LearningCausality.lean` ;
- variables contrôlées, consommation de la prédiction et verdicts de succession
  représentés dans les types du contrat ;
- constructeur générique du témoin causal depuis des données positives
  explicites, sans hypothèse cachée ;
- opérateur d’itération uniforme défini sans catalogue par profondeur ;
- conservation des occurrences et obligations requises ;
- succession du régime construite indépendamment puis raccordée à l’extension ;
- arrêt explicite lorsque le prochain cycle est impossible.

La Gate E est fermée pour les contrats et lois génériques. Les Gates G, I et J
sont fermées dans leur portée finie déclarée, et la Gate L construit désormais
l’invariant transformer à toute profondeur finie.

## 12. Lot F — Couche réflexive de la machine

### F1. Réutilisation du Cycle 2

Ne pas redémontrer le noyau diagonal. Construire un décodage des codes de la
machine vers ses statuts déterminés et réutiliser :

- `PullbackStatus` ;
- `transportRepresentation` ;
- `ReflectiveCircularStatusView` ou une généralisation minimale justifiée ;
- `diagonalStatus_notRepresentable` ;
- `noGlobalReflectiveClosure`.

### F2. Résultat cible

Montrer qu’une représentation exacte d’un régime et de sa norme déterminés
coexiste avec un statut extérieur au régime global de représentation.

### F3. Frontière

Ce résultat ne devra pas être présenté comme :

- une preuve qu’un modèle reconnaît empiriquement toutes ses erreurs ;
- une diagonalisation arithmétique ;
- une identité avec la sortie opérationnelle ;
- un générateur automatique de nouveau régime.

### Gate F

- instance machine de la représentation exacte ;
- sortie représentationnelle construite ;
- séparation typée avec la sortie opérationnelle ;
- aucune hypothèse de clôture globale réintroduite ailleurs.

## 13. Lot G — Modèle de référence fini

Avant toute réalisation neuronale, construire une petite instance calculable
satisfaisant les interfaces B à F :

- domaine fini ;
- histoires non triviales ;
- deux occurrences de même lecture mais de formations différentes ;
- questions futures capables de les séparer ;
- mémoire exacte relative à ces questions ;
- régime et norme indépendamment définis ;
- action admise et action rejetée ;
- cas distincts de formation impossible, sortie de régime et rupture normative ;
- paire causale parent–appris à contexte constitutif invariant ;
- deux cycles constitués par le même opérateur ;
- représentation exacte d’un statut déterminé ;
- sortie diagonale de représentation.

Ce modèle doit fermer les théorèmes sans dépendre d’un réseau. Il servira de
référence de test hors ligne, jamais de correcteur en ligne de l’instance
neuronale.

Ce modèle ferme d’abord le chemin non neuronal. Les réalisations neuronale et
transformer devront ensuite consommer exactement ses notions publiques, sans
dupliquer une sémantique simplifiée à côté d’elles.

### Gate G

- réduction Lean des cas positifs et négatifs ;
- absence de structures unitaires ou constantes rendant les lois vacuantes ;
- paire parent–appris à contexte invariant effectivement construite ;
- prédiction produite identique à l’entrée constitutive consommée ;
- propositions distinctes, rejet parent précis et succession apprise exacte ;
- deux cycles réellement liés par consommation du premier état produit ;
- première incorporation reconfigurant une donnée pertinente du second cycle ;
- façade non neuronale des lots B à F complète avant le début du lot H.

## 14. Lot H — Réalisation neuronale abstraite

### H1. Quatre plans

Définir :

```text
plan constitutif
plan formel et normatif
plan opérationnel
plan neuronal
```

Le plan neuronal ne reçoit qu’une vue autorisée. Les preuves, verdicts futurs,
cibles exactes et sorties d’audit doivent être absents de cette vue.

### H2. Proposition et élaboration

Séparer :

```text
état latent
→ proposition discrète
→ élaboration totale
→ candidat accepté ou première erreur localisée
```

L’élaboration ne répare jamais la proposition.

### H3. Fidélité

Construire un contrat de réalisation reliant les occurrences constitutives aux
objets opérationnels effectivement consommés. Une égalité de sortie finale ou
une similarité vectorielle ne suffit pas.

### H4. Causalité neuronale explicite

Avant l’audit, l’interface neuronale doit exposer la chaîne causale suivante
sans reconstruire ses valeurs après coup :

```text
état appris
→ prédiction neuronale
→ entrée constitutive consommée
→ proposition discrète
```

Les identités de ces quatre objets appartiennent à la trace primaire. Une simple
égalité de digests peut contrôler leur intégrité, mais ne remplace pas leur
relation typée.

### H5. Audit différé

La trace est produite et scellée avant audit. L’audit vérifie la fidélité mais
ne choisit, ne corrige et ne relance aucune étape.

### Tests séparateurs

- fuite de la cible dans la vue neuronale ;
- décodeur qui masque les candidats invalides ;
- reconstruction exacte cachée après la proposition ;
- prédiction correcte journalisée mais autre entrée réellement consommée ;
- proposition constante sous changement de l’état appris ;
- audit qui modifie l’arrêt ou le prochain état ;
- résultat terminal correct avec première divergence intermédiaire.

### Gate H

- vue neuronale explicitement bornée ;
- candidats invalides représentables et traçables ;
- premier échec localisé sans réparation ;
- fidélité définie sur la trajectoire complète ;
- contrat neuronal reliant l’état appris à la proposition consommée ;
- protocole d’audit causalement silencieux spécifié.

## 15. Lot I — Réalisation transformer

### I1. Position du transformer

Le transformer sera une instance du plan neuronal. Il pourra proposer et
transporter :

- occurrences ;
- dépendances ;
- rôles ;
- références de mémoire ;
- actions ;
- prédictions de conséquences.

Il ne définira pas l’identité, la norme ou l’admission par ses seuls logits.

### I2. Objets concrets

La première instance devra expliciter :

- tokens d’entrée ;
- activations ;
- état récurrent ou cache ;
- mémoire adressable ;
- proposition discrète ;
- trace de consommation ;
- relation avec les occurrences formelles.

### I3. Causalité requise

Les relations constitutives proposées doivent modifier le calcul futur. Une
structure seulement journalisée mais jamais consommée ne constitue pas une
réalisation.

### I4. Intervention parent–appris

La réalisation transformer doit exécuter une intervention contrôlée où restent
identiques :

- le problème prédictif ;
- l’état constitutif ;
- le producteur constitutif et ses paramètres ;
- son aléa ;
- le budget et les vues autorisées.

Seul l’état prédictif issu ou non de l’apprentissage varie. La réalisation doit
montrer la chaîne effective :

```text
variation de l’état appris
→ variation de la prédiction
→ consommation de cette prédiction
→ variation de la proposition constitutive
→ différence de verdict de succession
```

Une ablation qui modifie simultanément le contexte constitutif ne permet pas
d’attribuer causalement la différence à l’apprentissage.

### I5. Renommage

Les adresses techniques peuvent servir à retrouver les occurrences. La
computation doit rester équivariante sous renommage cohérent ; une adresse ne
doit pas devenir une identité sémantique cachée.

### Gate I

- un petit transformer consomme réellement une structure qu’il a proposée ;
- aucune cible interdite dans ses entrées ;
- intervention parent–appris préengagée avec contexte constitutif invariant ;
- prédictions et propositions différentes dans les deux branches ;
- identité vérifiée entre prédiction produite et entrée constitutive consommée ;
- rejet précis de la branche parent et succession exacte de la branche apprise ;
- intervention sur une relation active modifiant la continuation attendue ;
- renommage technique sans modification sémantique ;
- contrôle sans structure échouant sur la distinction ciblée.

La fermeture stricte comprend aussi `FreshProbeCausality.lean` : le corpus
d’entraînement et la sonde sont séparés, la sonde est liée par un engagement
unique, sa non-appartenance au corpus est réfutée constructivement, et le même
chemin parent–appris réutilise ensuite la consommation exacte et la succession
déjà établies. Les poids ainsi acquis sont ceux employés par la dynamique à
profondeur finie arbitraire.

## 16. Lot J — Mémoire, horizon long et rupture normative

### J1. Mémoire persistante

Démontrer sur l’instance que la mémoire conserve les différences requises par
les questions et continuations déclarées. Toute compression devra être liée à
un certificat de solidité causale dans cette portée.

### J2. Deux cycles liés et profondeur finie arbitraire — fermés

Exécuter plusieurs cycles avec le même opérateur, sans réintroduire les états
corrects entre les étapes. Mesurer séparément :

- fidélité de chaque transition ;
- conservation des occurrences ;
- obligations ouvertes et satisfaites ;
- première divergence ;
- état terminal.

Le premier état incorporé doit reconfigurer causalement le problème, les vues ou
la transition du cycle suivant. Deux succès successifs sur des problèmes fournis
indépendamment ne démontrent pas l’autonomie multicycle.

`TransformerDynamics.lean` ferme cette obligation pour deux cycles : le second
consomme la relation proposée au premier, et une ablation dédiée modifie sa
prédiction et sa proposition. `GovernedDynamics.lean` étend uniformément ce même
résultat à toute profondeur finie dans le lot L.

### J3. Rupture normative

Instancier et éprouver les trois diagnostics déjà séparés en amont :

```text
FormationFailure
RegimeExit
NormativeFailure
```

Une hallucination relative pourra être définie comme un candidat construit et
fidèlement réalisé dont la norme autonome est réfutée. Cette définition restera
relative à la norme explicitement choisie.

### J4. Confinement

Composer la rupture normative avec l’effectuation conditionnelle afin de
prouver qu’un candidat normativement rejeté ne peut produire l’effet gouverné.
Cela ne signifie pas que sa génération interne est impossible.

### Gate J

- diagnostics non confondus ;
- candidat rejeté conservé pour l’audit ;
- première obligation rompue localisée ;
- effet gouverné impossible sans satisfaction normative dérivée ;
- lien intercycle causal construit et détruit par une ablation dédiée ;
- aucune revendication générale sur toutes les hallucinations linguistiques.

La Gate J reste la fermeture de l’instance explicite à deux cycles. La Gate L,
distincte, est maintenant fermée pour la quantification sur tout `n : Nat`.

## 17. Lot K — Prototype exécutable et protocole expérimental

Ce lot a commencé après la fermeture des gates formels B à J.

### K1. Séparation des composants

```text
producteur neuronal
runtime constitutif exact
effecteur gouverné
journal immuable
auditeur différé
```

### K2. Gel préalable

Avant les runs confirmatoires, figer :

- architecture et paramètres ;
- données et splits ;
- règles de proposition et de départage ;
- vues neuronales autorisées ;
- intervention parent–appris et ablation intercycle ;
- variables maintenues identiques dans chaque comparaison causale ;
- graines ;
- métriques et seuils ;
- formats de trace ;
- scripts et empreintes.

### K3. Invariants expérimentaux

- l’état consommé est exactement l’état produit ;
- l’audit ne modifie aucun octet de la trajectoire ;
- les transitions revendiquées sont certifiables après coup ;
- une intervention constitutive active change le futur conformément à sa
  signification préengagée ;
- la prédiction produite est exactement l’entrée constitutive consommée ;
- le changement d’état appris précède et cause le changement de proposition ;
- le second cycle consomme et dépend causalement de l’état issu du premier ;
- un contrôle inerte ne produit pas cet effet ;
- les candidats invalides ne sont ni supprimés ni réparés.

### K4. Verdicts négatifs

Un échec de gate reste un résultat. Il doit localiser la première propriété
rompue et ne déclenche aucun changement silencieux du protocole.

### Gate K

- protocole reproductible depuis le dépôt ;
- plusieurs graines préengagées ;
- contrôles et ablations ;
- traces complètes ;
- audit différé ;
- rapport séparant faits, interprétation et limites.

La Gate K est temporairement réouverte. La version canonique unique est corrigée
en place avant intégration afin de séparer le corpus d’entraînement, la sonde de
smoke test et la sonde confirmatoire fixée. Le smoke test ne doit jamais
exécuter cette dernière avant le commit de gel. Aucun protocole parallèle n’est
créé. L’ancien résultat reste
récupérable dans l’historique Git mais ne peut plus servir de résultat du
protocole corrigé. Le nouveau run confirmatoire ne sera exécuté qu’après commit
du script et de la configuration définitifs.

## 18. Lot L — Dynamique gouvernée à profondeur finie arbitraire

Ce lot est fermé dans `GovernedDynamics.lean`. Il réutilise l’itération générique
déjà démontrée et ne crée aucune seconde notion d’histoire ou de cycle.

### L1. Atteignabilité proof-relevant

Définir l’atteignabilité à partir de `iterateHistory` ou directement comme une
histoire du `UniformTransition` concerné. Un état est atteignable uniquement si
la chaîne de transitions qui le forme est disponible ; l’égalité du seul état
terminal ne suffit pas.

### L2. Invariant gouverné agrégé

Définir une famille `GovernedInvariant` indexée par l’état réellement atteint et
réunissant sans les identifier :

- la fidélité de l’histoire et des occurrences consommées ;
- l’exactitude de la mémoire pour les futurs explicitement déclarés ;
- l’adéquation exacte entre régime et norme autonome à cet état ;
- la correspondance exacte entre proposition, action et contexte ;
- la nécessité d’un certificat indexé pour toute effectuation gouvernée ;
- la conservation du candidat rejeté et de la première rupture localisée.

Prouver d’abord la préservation à un pas, puis appliquer
`preservesAlongIteration` pour obtenir l’invariant après tout `n : Nat`. Le
théorème final doit quantifier sur la profondeur ; une liste d’exemples ne le
remplace pas.

### L3. Transformations admissibles

Une modification de la machine n’est pas alignée par le seul fait qu’elle est
appelée apprentissage. Définir un contrat `AdmissibleEvolution` séparant :

```text
mise à jour paramétrique
mise à jour de la mémoire
incorporation constitutive
succession du régime
évolution éventuelle de la norme
transport des actions et certificats
```

Une mise à jour paramétrique qui ne change pas le régime ni la norme doit le
déclarer dans son type. Si le régime ou la norme évoluent, leurs transports
respectifs doivent être fournis indépendamment et l’adéquation cible doit être
construite depuis ces transports et l’adéquation source. La norme cible ne doit
jamais être définie par copie de la décision du régime.

La revendication est existentielle et conditionnelle : seules les
transformations munies de ces témoins préservent l’alignement. Aucune loi ne doit
affirmer que toute mise à jour de poids, de mémoire ou de norme est admissible.

### L4. Instance transformer uniforme

Instancier l’opérateur déjà employé par `TransformerDynamics.lean` pour toute
profondeur finie. À chaque pas :

- le même cœur et les mêmes poids appris sont utilisés, sauf évolution
  explicitement admise par L3 ;
- la relation proposée au pas précédent est exactement la relation consommée ;
- la mémoire est celle produite par la mise à jour précédente ;
- aucune fixture correcte, cible ou décision d’audit n’est réinjectée ;
- une rupture normative reste représentée mais ne reçoit aucun effet gouverné.

L’ablation intercycle doit être formulée au rang arbitraire `k < n`. Lorsqu’une
condition explicite de sensibilité déclare qu’une relation et son ablation
produisent des calculs distincts au rang `k`, cette différence doit être
transportée vers le futur annoncé ; aucune différence ne doit être exigée sans
une telle condition. Une relation déclarée inerte doit rester sans effet.

### L5. Arrêt constructif

Lorsque la continuation n’est pas totale, employer `PartialTransition` et
produire soit le prochain pas, soit une réfutation de `CanAdvance`. Un arrêt
explicite satisfait le contrat ; une boucle supposée infinie ou un état terminal
injecté ne le satisfait pas.

### Tests séparateurs

- preuve limitée à deux cycles présentée comme quantification sur `Nat` ;
- état terminal correct avec histoire de formation absente ou différente ;
- obligation prouvée initialement mais non préservée à un pas intermédiaire ;
- poids modifiés tout en déclarant implicitement régime et norme inchangés ;
- norme cible reconstruite depuis le verdict du régime cible ;
- certificat transporté vers une action, un contexte ou une portée différents ;
- ablation remplaçant la relation retirée par une fixture correcte ;
- effet produit par une voie extérieure à l’effecteur gouverné.

### Gate L

- atteignabilité définie par une histoire réellement construite ;
- invariant agrégé non vacuant sur l’instance de référence ;
- loi de préservation à un pas constructive ;
- théorème à toute profondeur obtenu par l’itération générique existante ;
- instance transformer uniforme sans catalogue de profondeur ;
- évolution admissible distinguant paramètres, mémoire, régime et norme ;
- transport de l’adéquation construit, jamais supposé pour toute mise à jour ;
- arrêt partiel représenté positivement ;
- bloc `AXIOM_AUDIT` complet et vide de toute dépendance interdite.

La Gate L est fermée : `gateLCertificate` agrège ces obligations, les cas
séparateurs requis sont construits et l’audit axiomatique ne rapporte aucune
dépendance.

## 19. Lot M — Raffinement de la frontière exécutable

Ce lot relie l’exécution au noyau sans formaliser abusivement les calculs
flottants. Le producteur numérique reste une source de propositions ; la
frontière discrète, le runtime constitutif et l’effecteur gouverné portent les
obligations exactes.

### M1. Trace exécutable canonique

Définir un schéma versionné contenant les entrées autorisées, la proposition
discrète, la relation et la mémoire effectivement consommées, le diagnostic, le
certificat éventuel, l’effet éventuel et les empreintes de la trace scellée.
L’ordre causal doit être présent dans la trace primaire, pas reconstruit par
l’audit.

### M2. Relation de raffinement

Définir séparément :

```text
trace numérique observée
→ décodage discret total ou première erreur localisée
→ trace constitutive formelle
→ vérification de fidélité
→ admission et effectuation gouvernée
```

Le théorème de raffinement est conditionnel à un témoin vérifié du décodage et
de la fidélité. Il transfère les garanties du noyau à la trace discrète
effectivement consommée ; il ne transforme ni les logits, ni l’entraînement, ni
les performances numériques en théorèmes Lean.

### M3. Vérificateur et protocole expérimental unique

Conserver une seule version canonique du protocole dans l’arbre publié. Comme le
projet n’est pas encore intégré dans `main`, corriger cette version en place,
retirer son ancien résultat devenu incompatible, puis geler le protocole corrigé
par commit avant d’exécuter son unique run confirmatoire. Le vérificateur doit
refuser :

- une empreinte incorrecte ;
- un champ causal manquant ;
- une proposition réécrite après scellement ;
- une relation journalisée mais non consommée ;
- un effet sans certificat correspondant exactement à l’action et au contexte.

### Gate M

- schéma local, versionné et déterministe ;
- décodage total vers un succès ou une erreur localisée ;
- relation de raffinement portant sur toute la trajectoire discrète ;
- cas positif et cas négatifs reproductibles ;
- aucune cible normative dans la vue du producteur ;
- aucune génération de preuve par le réseau supposée fiable ;
- séparation explicite entre théorèmes Lean et observations flottantes ;
- séparation vérifiée entre corpus d’entraînement et sonde fraîche fixée ;
- séparation des sondes de smoke test et confirmatoire, sans exécution de la
  seconde avant le gel ;
- un seul protocole canonique et un seul résultat confirmatoire correspondant.

La partie Lean de la Gate M est fermée : `gateMCertificate` fournit le
raffinement exact et ses séparateurs formels. Sa partie exécutable sera refermée
quand le protocole canonique corrigé aura été commité, exécuté une fois en mode
confirmatoire, puis contrôlé en lecture seule. Aucun parseur JSON n’est invoqué
par Lean et aucun calcul flottant n’est promu au rang de théorème.

## 20. Phase scientifique ultérieure — hors gates internes

Après intégration vérifiée des Gates L et M dans `main` :

1. faire relire les déclarations et preuves Lean par des lecteurs indépendants ;
2. comparer précisément les contributions à la littérature pertinente ;
3. rédiger un article distinguant théorèmes, dérivations architecturales,
   implémentation et observations ;
4. étudier une réalisation de plus grande échelle dans une version expérimentale
   distincte.

Ces étapes sont nécessaires pour établir la réception, la nouveauté comparative
et la portée pratique. Elles ne changent ni la validité interne des théorèmes
déjà compilés ni leur périmètre formel.

## 21. Documentation bilingue

### 21.1 Ordre

1. stabiliser le français ;
2. vérifier ses ancrages Lean ;
3. produire l’anglais depuis cette version stabilisée ;
4. comparer la topologie des deux documents ;
5. mettre à jour les deux README ;
6. recalculer le manifeste.

### 21.2 Documents canoniques

```text
docs/fr/alignement_constitutif_transformers.md
docs/en/constitutive_transformer_alignment.md
```

Ces deux fichiers sont les documents canoniques. Toute extension des lots L et
M doit y être intégrée sans créer de texte scientifique concurrent.

### 21.3 Symétrie

Les versions française et anglaise doivent conserver :

- le même ordre logique ;
- les mêmes statuts ;
- les mêmes théorèmes et identifiants Lean ;
- les mêmes limites ;
- les mêmes instructions de reproduction.

## 22. Vérification finale

### 22.1 Formelle

- `lake build` ;
- contrôle de tous les blocs `AXIOM_AUDIT` ;
- recherche de `sorry`, axiomes et principes interdits ;
- vérification de l’ordre des imports ;
- réduction des exemples du modèle fini.

### 22.2 Documentaire

- liens locaux valides ;
- correspondance français–anglais ;
- aucune référence extérieure requise ;
- aucun statut exagéré ;
- auteurs placés en fin de document ;
- README cohérents avec la façade Lean.

### 22.3 Intégrité

- manifeste recalculé depuis l’état final ;
- script de vérification réussi ;
- plan et documents temporaires supprimés dans la merge request vers `main` ;
- registre temporaire, fragments bruts et espaces d’extraction absents ;
- aucun identifiant, chemin, import ou lien issu du corpus de travail interne ;
- comparaison finale de la branche avec `main` et résolution explicite de tout
  conflit sans écraser de modification extérieure au chantier ;
- `git diff --check` ;
- absence de fichiers générés ou caches ;
- état Git relu avant commit.

## 23. Ordre de travail et de commits restant

Les lots A à K appartiennent désormais au socle : ils doivent être relus et
réutilisés, pas réécrits. Chaque nouveau commit doit fermer une unité vérifiable :

1. dynamique gouvernée générique, atteignabilité et invariant à un pas ;
2. préservation à toute profondeur et instance transformer uniforme ;
3. transformations admissibles et transport de l’adéquation ;
4. correction du schéma exécutable canonique et relation formelle de raffinement ;
5. gel par commit, run confirmatoire unique, vérificateur et tests négatifs ;
6. mise à jour symétrique des documents français et anglais, des README, de
   l’audit et du manifeste ;
7. suppression du présent plan dans la demande de fusion vers `main`.

Le résultat confirmatoire corrigé ne sera exécuté qu’après commit du protocole
canonique. Son ajout au dépôt formera un commit ultérieur distinct du gel du
protocole ; aucune version parallèle ne sera conservée dans l’arbre publié.

Le plan temporaire peut apparaître dans l’historique de la branche de travail,
mais sa suppression doit faire partie de la merge request vers `main` et il ne
doit pas subsister dans l’arbre fusionné. Le registre de décision et les
fragments bruts ne doivent jamais être ajoutés à l’index Git.

## 24. Critères d’achèvement

### 24.1 Socle fini déjà fermé

Au commit de référence, le dépôt vérifie déjà la chaîne finie suivante :

```text
une histoire constitue des occurrences
→ une réalisation finie les transporte fidèlement
→ une mémoire distingue les futurs déclarés
→ régime et norme autonome sont exactement adéquats
→ une proposition apprise modifie la succession
→ deux cycles transformer consomment leur véritable lien intercycle
→ la rupture normative est localisée et conservée
→ aucun effet gouverné n’existe sans certificat exact
→ l’exactitude déterminée coexiste avec la non-clôture réflexive globale
```

Ce socle ne doit pas être présenté comme encore hypothétique, ni comme une
preuve portant déjà sur tout transformer ou toute profondeur.

### 24.2 Extension formelle fermée sur la branche

L’extension implémentée sur la branche permet désormais de vérifier la chaîne
suivante sans ressource scientifique extérieure :

```text
une histoire constitue des occurrences
→ une réalisation neuronale les transporte fidèlement
→ une mémoire conserve les différences nécessaires aux futurs déclarés
→ un régime décide l’admission
→ une norme autonome contrôle ce régime
→ une effectuation dépend d’un certificat exact
→ un apprentissage modifie une prédiction effectivement consommée
→ cette prédiction modifie la proposition constitutive suivante
→ un cycle produit et consomme son véritable état successeur
→ pour tout n, les n cycles sont formés par le même opérateur
→ l’invariant gouverné est préservé sur tous leurs états atteignables
→ toute évolution de machine utilisée possède ses transports admissibles
→ l’adéquation cible est construite depuis l’adéquation source
→ les ruptures restent représentables et localisées
→ aucune rupture normative ne peut recevoir un effet gouverné sans certificat
→ certains statuts sont représentés exactement
→ aucune clôture réflexive globale n’est postulée
→ toute trace exécutable revendiquée raffine la trace discrète formelle consommée
```

La réussite d’un seul étage, un score terminal, une documentation persuasive ou
une compilation isolée ne suffit pas. La fermeture exige les interfaces, leurs
compositions, les modèles séparateurs, l’instance finie, la réalisation
transformer, l’invariant à toute profondeur, les transformations admissibles,
le raffinement exécutable, les traces reproductibles et la discipline exacte
des revendications.

### 24.3 Fusion terminale

La tâche globale n’est pas terminée par la seule ouverture d’une merge request.
Après fermeture de toutes les gates :

1. comparer la branche `codex/constitutive-transformer` à `main` ;
2. vérifier le diff complet et l’absence des documents temporaires dans l’arbre
   résultant ;
3. ouvrir ou finaliser la merge request vers `main` ;
4. obtenir la validation explicite de l’utilisateur pour la fusion ;
5. fusionner la branche dans `main` ;
6. exécuter sur le commit fusionné `lake build`, l’audit axiomatique, la
   vérification documentaire et le contrôle du manifeste ;
7. confirmer que la tête de `main` contient exactement le résultat validé.

Un conflit non résolu, une gate rouverte, un document temporaire restant ou un
échec post-fusion signifie que le chantier n’est pas achevé.
