# Plan temporaire — Reconstruction constitutive de la couche transformer

## 0. Statut du document

Ce document organise le chantier sur la branche
`codex/constitutive-transformer-reconstruction` après son rebase sur `main`
(`07866f5`). Il ne constitue ni une preuve, ni un résultat scientifique, ni une
source canonique du dépôt.

Le plan doit être supprimé dans la merge request qui intégrera le chantier dans
`main`. Sa suppression, le recalcul du manifeste et la vérification de l’état
fusionné font partie de la définition d’achèvement.

État au 15 septembre 2026 :

- le socle structurel et sa persistance finie de Cycle 1 sont présents ;
- une couche `ConstitutiveAlignment/` existe sur la branche, mais elle est
  provisoire et ne vaut pas encore comme réalisation du Cycle 1 ;
- aucun résultat de cette couche ne doit être conservé pour protéger un travail
  antérieur ; chaque déclaration peut être réécrite ou supprimée ;
- l’implémentation scientifique ne reprend qu’après fermeture de la Gate 0.

## 1. Décision architecturale centrale

Il n’existera qu’une seule chaîne constitutive dans le dépôt : celle qui est
déjà construite par Cycle 1.

```text
CircularPresentation
        ↓
PositiveConstitution
        ↓ GeneratedStep / generate
RootedGeneratedHistory
        ↓ itération réelle
IteratedConstitutivePersistence.iteratedHistory P n
        ↓ index exact
IteratedCarrier Initial n
        ↓ réalisation indépendante
ConcreteContinuationAlgebra P
        ↓ instance particulière
réalisation transformer
        ↓ seulement après constitution
mémoire, propositions et readouts
        ↓ contrôle indépendant
régime, norme et effectuation
        ↓ observation des statuts
réflexivité et non-clôture globale
```

Le transformer n’engendre pas l’identité constitutive, ne définit pas la norme
et ne remplace pas le producteur de Cycle 1. Il réalise une construction déjà
constituée. Ses sorties ne peuvent être invoquées pour fabriquer après coup les
témoins structurels qui autorisent ces mêmes sorties.

Cette décision interdit trois architectures concurrentes :

1. une seconde histoire définie spécialement pour les transformers ;
2. une récursion en `Nat` parallèle à `iteratedHistory` ;
3. un domaine programmatique utilisé comme fondation de la constitution.

## 2. Autorité formelle déjà disponible

### 2.1 Constitution et histoire

`StrongPerimetralTurning.lean` construit notamment :

- `PositiveConstitution P` ;
- `GeneratedStep source target` ;
- `generate` et `appendGenerated` ;
- les histoires proof-relevant `History` et `RootedGeneratedHistory` ;
- la provenance historique, la fraîcheur de formation et l’obstruction de
  clôture transportée ;
- le régime `CircularRefinement`, la norme autonome
  `CircularSpecificationSatisfaction` et leur adéquation exacte ;
- les réalisations concrètes au moyen de `ConcreteContinuationAlgebra` et
  `ExactHistoryInterpretation`.

Ces objets restent les objets scientifiques de référence. La couche transformer
doit les importer et les instancier ; elle ne doit pas les recopier.

### 2.2 Persistance constitutive

Les modules de `main` ferment déjà les obligations abstraites suivantes :

- `Alignment.Constitutive` : séparation constitution/réalisation et extension
  exacte `Initial ⊕ Unit ≃ Extended` ;
- `Alignment.FinitePersistence` : une identité fraîche par étape, persistance
  de chaque identité antérieure, indépendance du témoin de profondeur et
  cohérence des transports ;
- `Alignment.ReadoutPersistence` : ajout des valeurs après constitution et
  conservation des distinctions déjà établies ;
- `Cycle1.ConstitutivePersistence` : instanciation canonique au premier pas
  réel après le périmètre ;
- `Cycle1.IteratedConstitutivePersistence` : instanciation sur les histoires
  réellement produites par Cycle 1 pour tout `n : Nat` ;
- `StructuralEntrypoint` : façade publique des mêmes résultats.

La profondeur finie arbitraire n’est donc plus une obligation à recréer. La
nouvelle obligation est de construire un transformer qui habite honnêtement la
couche de réalisation de ce socle.

### 2.3 Ce qui n’est pas encore prouvé

Le socle ne prouve pas encore :

- qu’une architecture donnée est réellement un transformer ;
- qu’un calcul d’attention réalise les étapes de Cycle 1 ;
- qu’une mémoire neuronale conserve des valeurs, et non seulement des
  identités ;
- qu’une proposition transformer est causalement consommée par la transition
  suivante ;
- qu’une sortie effectuée satisfait une norme déterminée ;
- l’absence universelle d’hallucinations dans les transformers ;
- une garantie empirique sur un modèle entraîné à grande échelle.

Chaque revendication devra être reliée à une déclaration Lean précise. Le mot
« non-hallucination » ne sera employé que pour une propriété formelle relative
à une norme et à une loi d’effectuation explicitement définies.

## 3. Invariants non négociables

### 3.1 Constructivité et calculabilité

Tout fichier Lean créé ou modifié doit :

- rester sans `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`,
  `propext` ou `Quot.sound` ;
- construire positivement ses témoins ;
- garder exécutables les définitions qui produisent des données dans `Type` ;
- contenir exactement un bloc `AXIOM_AUDIT` à sa toute fin ;
- compiler avec le toolchain épinglé du dépôt.

Une interface conditionnelle est permise comme interface. Une gate concrète
n’est fermée que par une instance effectivement construite dans le dépôt.

### 3.2 Séparations de types

Les distinctions suivantes doivent être visibles dans les signatures :

```text
constitution             ≠ réalisation transformer
identité                  ≠ activation ou valeur
persistance d’identité    ≠ conservation de valeur
proposition               ≠ incorporation
incorporation             ≠ succession constitutive
admission                 ≠ satisfaction normative
diagnostic                ≠ blocage de l’effectuation
sortie opérationnelle     ≠ sortie représentationnelle
OOD structurel            ≠ diagonalisation réflexive
preuve Lean               ≠ observation expérimentale
```

### 3.3 Interdiction de la circularité justificative

Aucune preuve ne peut suivre le schéma suivant :

```text
le transformer émet x
→ x reçoit une étiquette acceptable
→ cette étiquette justifie rétroactivement l’émission de x
```

La direction obligatoire est :

```text
objet constitué indépendamment
→ réalisation exacte
→ proposition calculée
→ vérification par une norme autonome
→ certificat
→ effectuation autorisée
```

### 3.4 Une seule version canonique

Il n’y aura ni suffixes `V2`, `New`, `Bis`, `Legacy`, ni deux familles
concurrentes exprimant la même notion. Lorsqu’une abstraction actuelle est
faussement ciblée, elle est remplacée et ses usages sont migrés dans le même
lot. Le build ne doit jamais choisir silencieusement entre deux versions.

## 4. Disposition de la couche actuelle

Tous les fichiers ci-dessous sont provisoires jusqu’à leur gate. « Réécrire »
autorise leur remplacement complet.

| Fichier actuel | Décision | Rôle après reconstruction |
|---|---|---|
| `Machine.lean` | réécrire | façade paramétrée par `P` et par une réalisation du vrai Cycle 1 |
| `Succession.lean` | remplacer | aucune itération propre ; réexport ciblé de l’itération Cycle 1 |
| `NeuralRealization.lean` | réécrire | contrat neuronal produisant un `ConcreteContinuationAlgebra P` |
| `TransformerRealization.lean` | réécrire | instance transformer calculable et non dégénérée du contrat |
| `TransformerDynamics.lean` | réécrire | conséquences à toute profondeur obtenues par `cycle1Realization` |
| `CausalMemory.lean` | réécrire | mémoire indexée par les identités persistantes du Cycle 1 |
| `LearningCausality.lean` | conserver seulement après raccord | intervention parent/appris sans changer les autres variables |
| `FreshProbeCausality.lean` | conserver seulement après raccord | protocole causal postérieur à la constitution |
| `NormativeExecution.lean` | réécrire | certificat autonome avant effectuation |
| `NormativeFailure.lean` | réécrire | localisation typée d’une rupture normative |
| `GovernedDynamics.lean` | réécrire | composition de la réalisation, de la mémoire et de l’exécuteur |
| `ReflectiveMachine.lean` | retargeter | observation des statuts puis application du noyau de Cycle 2 |
| `ReferenceModel.lean` | auditer | instance finie de test, jamais fondation du résultat générique |
| `ExecutableRefinement.lean` | auditer après la norme | raffinement d’exécution, sans redéfinir l’admission |
| `TypedProgramDomain.lean` | déplacer conceptuellement en application | domaine fini optionnel, sans import vers le noyau transformer |
| `EndogenousTypedSuccession.lean` | reporter | application ultérieure du domaine typé, après toutes les gates du noyau |
| `VerificationTransport.lean` | isoler | pipeline de vérification en aval, sans rôle constitutif |

Les petits résultats actuellement valides peuvent être réutilisés uniquement
s’ils se raccordent définitionnellement au nouveau graphe. Une ressemblance de
vocabulaire ou un théorème booléen isolé ne suffit pas.

## 5. Graphe d’imports cible

```text
ExactTypeTransport
        ↓
Alignment.Constitutive
        ↓
Alignment.FinitePersistence
        ↓
Alignment.ReadoutPersistence ───────────────┐
                                            ↓
StrongPerimetralTurning ──→ Cycle1.ConstitutivePersistence
                                            ↓
                          Cycle1.IteratedConstitutivePersistence
                                            ↓
                          ConstitutiveAlignment.Machine
                                            ↓
                          NeuralRealization
                                            ↓
                          TransformerRealization
                                ├───────────┐
                                ↓           ↓
                         CausalMemory  LearningCausality
                                └─────┬─────┘
                                      ↓
                             TransformerDynamics
                                      ↓
                             NormativeExecution
                                      ↓
                              GovernedDynamics
                                      ↓
                             ReflectiveMachine
```

Contraintes :

- aucun module `Alignment/*` ou `Cycle1/*` n’importe
  `ConstitutiveAlignment/*` ;
- `TypedProgramDomain` et `VerificationTransport` restent des feuilles ;
- `ReflectiveMachine` importe Cycle 2, mais aucun résultat de Cycle 2 ne sert à
  fabriquer l’adéquation de Cycle 1 ;
- l’agrégateur `ConstitutiveAlignment.lean` ne contient pas de preuve propre.

## 6. Théorèmes de raccord obligatoires

Le raccord n’est pas une phrase documentaire. Il doit être constitué par des
déclarations du type suivant, avec les noms définitifs choisis pendant
l’implémentation :

```lean
def transformerAlgebra
    (P : CircularPresentation)
    (implementation : TransformerImplementation P) :
    ConcreteContinuationAlgebra P

def transformerRealizationAt
    (P : CircularPresentation)
    (implementation : TransformerImplementation P)
    (n : Nat) :
    (IteratedConstitutivePersistence.cycle1Alignment P n).Realization

theorem transformerRealizationAt_eq_cycle1Realization ...

theorem transformerPreviousIdentityPersists ...

theorem transformerFreshIdentityIsNew ...

theorem transformerExtensionNaturality ...

theorem transformerDepthWitnessIndependent ...
```

`transformerRealizationAt` doit être obtenu à partir de
`IteratedConstitutivePersistence.cycle1Realization`, appliqué à
`transformerAlgebra`. Toute construction indépendante d’une histoire de tokens
ou de couches à côté de `iteratedHistory` échoue à cette gate.

## 7. Lot 0 — Stabilisation de la base

### Travaux

1. Vérifier que `main` est ancêtre de la branche.
2. Compiler l’arbre rebased sans modifier les sources.
3. Recalculer les décomptes d’audits issus de la réunion des deux branches.
4. Vérifier l’absence des mots-clés interdits et l’unicité des blocs d’audit.
5. Produire un registre temporaire `KEEP / REWRITE / DELETE` au niveau des
   déclarations de `ConstitutiveAlignment/`.
6. Supprimer ce registre avant la merge request.

### Gate 0

- `main` est ancêtre de la branche ;
- build vert ;
- aucun axiome ou mot-clé interdit ;
- aucun fichier scientifique du socle n’a été réécrit pour accommoder
  l’ancienne couche transformer ;
- la liste exacte des déclarations à remplacer est connue.

## 8. Lot 1 — Machine constitutive raccordée au Cycle 1

### Travaux

1. Remplacer la notion actuelle de machine par une façade de
   `CircularPresentation`, `iteratedHistory`, `cycle1Alignment` et
   `cycle1Realization`.
2. Exposer le stade `n`, le passage `n → n+1`, l’ancienne identité et
   l’identité fraîche sans définir un second type d’histoire.
3. Prouver la compatibilité exacte du cas de profondeur un avec
   `canonicalOneStepAlignmentRealization` dans les deux directions.
4. Réutiliser les théorèmes d’indépendance des témoins et de cohérence des
   transports plutôt que les reformuler comme hypothèses.

### Séparateurs

- une application d’occurrences constante ou quotientée ne peut pas réaliser
  l’exactitude old/fresh ;
- une projection qui oublie une occurrence ne possède pas de transport exact ;
- une permutation arbitraire des identités ne peut pas être déclarée naturelle
  sans le carré de transport correspondant.

### Gate 1

La façade ne contient plus aucune succession parallèle. Tous ses stades et
toutes ses identités se réduisent aux objets du Cycle 1.

## 9. Lot 2 — Contrat neuronal et instance transformer

### 9.1 Contrat neuronal

Définir une interface minimale qui distingue :

- paramètres ;
- état résiduel ;
- mémoire adressable ;
- requête, clés et valeurs ;
- score d’attention et sélection ;
- proposition ;
- mise à jour de l’état ;
- interprétations des rôles structurels.

L’interface doit construire un `ConcreteContinuationAlgebra P`. Les champs de
compatibilité, provenance, continuation de différence et fraîcheur ne peuvent
pas être remplis uniformément par `Unit` lorsqu’ils portent une revendication
utilisée ensuite.

### 9.2 Instance transformer minimale mais réelle

Construire une instance finie, totale et exécutable comportant effectivement :

- un calcul de requête, clé et valeur ;
- une sélection d’attention ;
- une connexion résiduelle ;
- un état de paramètres parent et un état appris distincts ;
- une proposition calculée à partir de l’état autorisé ;
- une transition qui consomme la proposition sélectionnée.

L’instance peut utiliser des types finis et une attention dure. Elle ne peut
pas être un renommage d’une fonction booléenne sans structure d’attention.

### Séparateurs

- ablation de la relation réellement consommée : la transition pertinente
  change ;
- relation inerte : la transition ne change pas ;
- renommage cohérent des adresses : le comportement observable est conservé ;
- collision de deux identités : l’exactitude de réalisation devient
  impossible ;
- proposition remplacée après calcul : la loi de consommation échoue.

### Gate 2

Une instance calculable produit le `ConcreteContinuationAlgebra` attendu,
compile sans hypothèse ouverte et ferme tous les séparateurs.

## 10. Lot 3 — Réalisation à profondeur finie arbitraire

### Travaux

1. Définir `transformerRealizationAt` par le vrai `cycle1Realization`.
2. Prouver pour tout `n` :
   - persistance de chaque identité antérieure ;
   - distinction de l’identité fraîche ;
   - naturalité entre deux réalisations transformer ;
   - indépendance du témoin `DepthExtension` ;
   - cohérence de composition des transports.
3. Déduire le cas à un pas des théorèmes génériques, sans preuve concurrente.

### Gate 3

Il existe un seul opérateur transformer et une seule preuve quantifiée sur
`n : Nat`. Aucun catalogue de profondeurs et aucune preuve limitée à deux cycles
ne subsistent dans le noyau.

## 11. Lot 4 — Mémoire constitutive

### 11.1 Deux niveaux à distinguer

```text
identité mémorielle persistante
        ≠
valeur lue à cette identité
```

L’index de mémoire doit être transporté par `IteratedCarrier` et les spokes
exacts. Les valeurs sont attachées ensuite par `FiniteFreshValues` et
`iteratedReadout`, ou par une abstraction démontrée équivalente.

### 11.2 Obligations

- une cellule ancienne reste adressable à toute profondeur ultérieure ;
- sa valeur n’est dite conservée que si la mise à jour le prouve explicitement ;
- deux identités distinguées par un readout restent distinguées après extension ;
- le changement de réalisation réindexe la mémoire sans inventer une
  correspondance pair-à-pair ;
- les futurs pertinents sont une famille explicite, pas l’ensemble implicite de
  toutes les questions imaginables.

### Séparateurs

- un encodage constant conserve un nombre de cellules mais pas leur identité ;
- une mise à jour qui écrase une ancienne valeur ne satisfait pas la conservation
  de valeur ;
- deux états au même readout présent mais aux futurs pertinents différents ne
  peuvent pas être contractés par une mémoire déclarée exacte.

### Gate 4

La persistance d’identité et la conservation de valeur possèdent deux théorèmes
distincts et deux contre-modèles distincts.

## 12. Lot 5 — Causalité de l’apprentissage et succession

### Travaux

1. Fixer avant comparaison le corpus, l’entrée, la mémoire, la norme et la sonde.
2. Faire varier uniquement les paramètres parent/appris.
3. Montrer que la prédiction change sur une sonde fraîche fixée.
4. Montrer que la proposition provient exactement de cette prédiction.
5. Montrer que la transition suivante consomme cette proposition.
6. Relier la transition obtenue au pas `GeneratedStep` réalisé, et non à une
   transition auxiliaire.

### Gate 5

Le lien causal complet est :

```text
apprentissage
→ paramètres modifiés
→ attention/prédiction modifiée
→ proposition modifiée
→ proposition consommée
→ réalisation du pas constitutif suivant
```

Chaque flèche est une déclaration séparée. Une simple juxtaposition de traces
parent/appris ne ferme pas la gate.

## 13. Lot 6 — Norme, admission et effectuation

### 13.1 Pipeline obligatoire

```text
TransformerProposal
        ↓ décodage fidèle
Candidate
        ↓ régime opérationnel
AdmissionStatus
        ↓ norme autonome sur le même candidat
NormStatus
        ↓ adéquation démontrée
AuthorizationCertificate
        ↓ seul constructeur public de l’effet
EffectuatedTransition
```

La norme ne reçoit ni l’étiquette produite par le transformer, ni un certificat
fabriqué par l’exécuteur. Elle examine le même objet que le régime par une voie
indépendante.

Deux niveaux normatifs doivent rester distincts :

1. au niveau structurel, le candidat est un `RootedGeneratedHistory P`, le
   régime est `CircularRefinement P` et la norme est
   `CircularSpecificationSatisfaction P` ; leur adéquation est déjà démontrée ;
2. au niveau d’une proposition transformer, le candidat opérationnel reste
   indexé par l’histoire et par l’occurrence constituées, mais sa norme d’action
   doit être définie et prouvée séparément.

Le second niveau n’hérite pas automatiquement de l’adéquation du premier. Un
pont explicite est requis si une propriété structurelle est utilisée dans une
autorisation d’action. Inversement, une autorisation d’action ne modifie jamais
le statut structurel de l’histoire.

### 13.2 Résultats cibles

- soundness : toute admission certifiée satisfait la norme ;
- completeness relative : toute satisfaction normative déterminée reconstruit
  l’admission correspondante lorsque le cadre l’autorise ;
- non-effectuation : une réfutation normative empêche de construire l’effet ;
- localisation : la rupture est attachée au candidat et à son étape exacte ;
- continuation : la construction peut continuer hors du régime sans être
  présentée comme effectuée normativement.

### 13.3 Portée du terme hallucination

Le seul énoncé admissible est de la forme :

```text
dans ce système formel et relativement à cette norme,
aucune sortie effectuée ne possède un statut normatif réfuté
```

Cela ne signifie ni vérité universelle des textes, ni absence statistique
d’erreurs, ni garantie sur tout transformer.

### Séparateurs

- validation du seul état cible ;
- inversion de la source et de la cible ;
- étiquette normative ajoutée après la proposition ;
- certificat forgé sans adéquation ;
- diagnostic correct mais effet néanmoins exécutable ;
- admission et norme appliquées à deux candidats différents.

### Gate 6

Tous les séparateurs sont rejetés constructivement et le seul chemin public
vers `EffectuatedTransition` exige le certificat exact.

## 14. Lot 7 — Couche réflexive

La réflexivité vient après l’adéquation opérationnelle.

1. Observer propositionnellement les statuts déjà définis.
2. Transporter l’adéquation Cycle 1 vers leurs codes.
3. Instancier `Cycle2.ReflectiveAlignment` sur ces statuts.
4. Conserver séparés :
   - la représentation exacte des statuts déterminés ;
   - le statut diagonal extérieur ;
   - l’absence de clôture réflexive globale.

Interdictions :

- aucune implication de l’OOD opérationnel vers la diagonalisation ;
- aucune utilisation de la diagonalisation pour prouver rétroactivement la
  norme ;
- aucune assimilation de la non-clôture globale à une défaillance locale de
  l’alignement.

### Gate 7

Le raccord à Cycle 2 passe uniquement par les statuts représentés et les
théorèmes existants de transport de l’adéquation.

## 15. Lot 8 — Applications optionnelles

`TypedProgramDomain`, `EndogenousTypedSuccession` et `VerificationTransport`
ne sont traités qu’après les Gates 0 à 7.

Ils doivent alors :

- importer l’architecture stabilisée sans être importés par elle ;
- utiliser les identités et histoires du Cycle 1 ;
- distinguer programme, abstraction, proposition, incorporation et exécution ;
- posséder une sémantique totale et exécutable ;
- ne pas élargir les revendications du noyau transformer.

S’ils ne peuvent pas satisfaire ces conditions sans duplication, ils sont
retirés de la livraison principale plutôt que maintenus comme seconde théorie.

### Gate 8

Chaque application conservée est une feuille raccordée par des transports
explicites au noyau stabilisé. Toute application qui exige une seconde histoire,
une seconde notion d’identité ou une norme circulaire est supprimée.

## 16. Matrice adversariale obligatoire

| Test | Construction fautive | Résultat exigé |
|---|---|---|
| C1 | application d’occurrences constante ou quotientée | impossible d’obtenir l’exactitude old/fresh |
| C2 | labels ajoutés après calcul | aucune reconstruction du témoin constitutif |
| C3 | validation du seul état cible | aucune autorisation de transition |
| C4 | deux cycles codés en dur | ne satisfait pas la quantification uniforme en `Nat` |
| C5 | readout utilisé comme identité | ne construit pas le spoke exact requis |
| C6 | mémoire ancienne écrasée | échoue à la conservation de valeur |
| C7 | transport dépendant du chemin | contredit la cohérence de composition |
| C8 | certificat normatif forgé | ne construit pas `EffectuatedTransition` |
| C9 | OOD assimilé au diagonal | aucun terme du type d’implication revendiqué |

Chaque test doit être un terme Lean positif, une réfutation constructive ou un
test exécutable gelé selon la nature de l’obligation. Un commentaire affirmant
qu’un cas est impossible ne compte pas.

## 17. Documentation bilingue

Les documents canoniques sont mis à jour seulement après stabilisation des noms
Lean :

- `docs/fr/alignement_constitutif_transformers.md` ;
- `docs/en/constitutive_transformer_alignment.md` ;
- `README_fr.md` ;
- `README.md`.

Ordre interne du document scientifique :

1. problème architectural ;
2. socle Cycle 1 effectivement utilisé ;
3. transformer comme réalisation ;
4. persistance des identités ;
5. mémoire et valeurs ;
6. causalité d’apprentissage ;
7. norme et effectuation ;
8. couche réflexive ;
9. portée exacte et reproduction ;
10. déclaration d’auteur à la fin.

Les versions française et anglaise doivent avoir la même structure, les mêmes
théorèmes cités, les mêmes réserves et les mêmes instructions de reproduction.

## 18. Vérification et intégration

### 18.1 Après chaque lot Lean

```text
lake build
scan des mots-clés interdits
vérification d’un bloc AXIOM_AUDIT par fichier
inspection des sorties #print axioms
tests positifs
tests séparateurs
```

### 18.2 Avant la merge request

- exécuter le build complet des trois bibliothèques ;
- vérifier toutes les sources Lean ;
- exécuter les tests et protocoles gelés ;
- vérifier les liens locaux et la symétrie bilingue ;
- supprimer ce plan et tous les registres temporaires ;
- recalculer `MANIFEST.sha256` depuis l’arbre final ;
- mettre à jour `audit/AUDIT_BUILD.txt` avec les vrais décomptes ;
- vérifier un diff propre contre `main` ;
- confirmer qu’aucun cache, fragment brut ou chemin extérieur n’est publié.

### 18.3 Après fusion explicitement autorisée

- vérifier la tête fusionnée de `main` ;
- relancer `lake build` sur ce commit ;
- revérifier le manifeste ;
- confirmer l’absence du présent plan dans l’arbre publié.

## 19. Ordre d’exécution

```text
Gate 0  base rebased et auditée
   ↓
Gate 1  machine raccordée au vrai Cycle 1
   ↓
Gate 2  instance transformer exacte et calculable
   ↓
Gate 3  réalisation uniforme à profondeur finie arbitraire
   ↓
Gate 4  mémoire : identité puis valeur
   ↓
Gate 5  causalité apprentissage → succession réelle
   ↓
Gate 6  norme autonome → certificat → effectuation
   ↓
Gate 7  observation réflexive sans fausse implication
   ↓
Gate 8  applications optionnelles
   ↓
documentation bilingue
   ↓
audit final, suppression du plan, merge request
   ↓
fusion autorisée et vérification de `main`
```

Une gate non fermée bloque les lots qui en dépendent. Elle ne doit pas être
contournée par une hypothèse, une nouvelle version du même type ou une
revendication documentaire affaiblie après coup.

## 20. Critère d’achèvement scientifique

Le chantier est achevé lorsque le dépôt construit, sans axiome et sans seconde
chaîne constitutive :

1. un transformer fini réel comme `ConcreteContinuationAlgebra` du Cycle 1 ;
2. sa réalisation exacte des histoires produites pour tout `n : Nat` ;
3. la persistance des identités et, séparément, les conditions de conservation
   des valeurs mémorielles ;
4. une chaîne causale complète de l’apprentissage à la succession réalisée ;
5. une effectuation impossible lorsqu’une norme autonome réfute le candidat ;
6. un transport réflexif des statuts compatible avec la non-clôture globale ;
7. les neuf séparateurs adversariaux ;
8. une documentation bilingue dont chaque revendication renvoie à sa
   déclaration Lean exacte.

Jusqu’à cette fermeture, le dépôt possède une base structurelle forte et des
éléments transformer exploratoires ; il ne possède pas encore la théorie
transformer constitutive achevée décrite ici.
