# Plan d’implémentation — audit constitutif avec ConLeche

## Statut

Ce document est un document de chantier temporaire.

Il organise l’ajout de deux résultats distincts :

1. un audit externe reproductible du dépôt avec ConLeche en mode `--verified` ;
2. une étude constitutive de la frontière entre le source Lean et l’objet effectivement présenté au checker.

Il doit être supprimé dans la pull request ou merge request qui intégrera le
chantier dans `main`. Il ne fait pas partie des livrables scientifiques finaux.

La branche de chantier `codex/con-leche-constitutive-audit` a été créée depuis
`codex/constitutive-transformer` au commit `794b818`. Elle dépend donc de ce
socle tant que celui-ci n’a pas été intégré à `main`. Avant la merge request
finale, vérifier explicitement que sa base contient ce commit et tous les
résultats scientifiques attendus.

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

## 2. Deux lignes de travail indépendantes

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
et la fidélité amont restent deux certificats séparés.

La Ligne A peut être fermée même si la Ligne B demeure ouverte. Aucun succès de
l’une ne doit être présenté comme un succès de l’autre.

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

- `StrongPerimetralTurning.History` pour les histoires proof-relevant lorsque
  son carrier homogène convient naturellement ;
- `ConstitutiveAlignment.InjectiveMap` et `InjectiveMap.trans` pour la
  conservation des distinctions d’occurrences ;
- les transports d’occurrences déjà prouvés dans le Cycle 1 ;
- `ConstitutiveAlignment.Separators.noFaithfulTerminalOnlyRealization` comme
  séparateur générique déjà acquis entre lecture terminale et réalisation fidèle.

Pour les quatre carriers hétérogènes du pipeline, une petite structure locale
est admise si l’encodage dans `History` exige une somme artificielle ou masque les
types. Cette structure doit alors être un adaptateur spécialisé, pas un nouveau
noyau concurrent.

## 4. Portée exacte des résultats

### Démontré dans Lean

- les relations de fidélité sont distinctes des fonctions de transformation ;
- leurs témoins se composent explicitement ;
- l’acceptation terminale ne permet pas de reconstruire une origine fidèle ;
- une substitution déterminée est rejetée par le certificat de fidélité ;
- un verdict peut être rapporté au source uniquement dans la portée transportée
  par les témoins disponibles.

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
- une sécurité cryptographique ou matérielle de toute la chaîne.

## 5. Gate 0 — gel et compatibilité

### État initial connu

```text
dépôt local : Lean v4.33.1
branche principale ConLeche observée lors de la préparation : Lean v4.33.0
```

Cet état est un constat de préparation, pas un gel de version. Il doit être
relevé à nouveau avec les commits exacts au début de l’implémentation. La
différence observée interdit de supposer la compatibilité.

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

## 8. Gate 3 — noyau formel spécialisé du transport

### Fichier envisagé

```text
ConstitutiveAlignment/VerificationTransport.lean
```

### Interface minimale envisagée

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

## 10. Gate 5 — cas d’étude ConLeche réel

### Cible initiale

La première cible envisagée est la réécriture localisée d’une fonction de
projection vers une forme utilisant un recursor.

Elle n’est retenue définitivement qu’après lecture du code exact au commit
épinglé.

L’unité de l’étude doit être fixée avant la formalisation. Le candidat initial
est une occurrence de déclaration située dans un flux ordonné, avec son nom, sa
position et le contexte antérieur pertinent. Une expression isolée de son
préfixe d’environnement ne suffit pas pour revendiquer une étude fidèle du cas
réel.

### Étapes obligatoires

1. identifier la fonction amont exacte et ses types d’entrée/sortie ;
2. inventorier les déterminations qu’elle prétend conserver ;
3. déterminer ce qui est vérifié ensuite par le fold ;
4. écrire une spécification locale minimale de fidélité ;
5. reconstruire uniquement le fragment nécessaire dans le vocabulaire du dépôt ;
6. produire un exemple fidèle ;
7. produire une mutation non fidèle ;
8. vérifier que le certificat rejette la mutation ;
9. établir séparément la correspondance entre le fragment local et le
   comportement amont observé ou prouvé.

### Règle de revendication

Sans correspondance établie avec l’implémentation épinglée, le résultat doit être
présenté comme un modèle de la transformation documentée, pas comme une preuve
portant sur l’implémentation complète de ConLeche.

La Gate 5 ne couvre jamais implicitement les autres transformations du frontend.

### Gate 5b — minimisation relative à `no False`

La minimisation porte sur une famille finie de déterminations explicitement
choisie pour le cas d’étude. Elle ne prétend pas trouver une structure minimale
absolue parmi toutes les représentations possibles.

Le transport négatif à établir a la forme suivante :

```text
chaque occurrence source de type False
  → une occurrence présentée correspondante de type False

aucune occurrence présentée de type False
  → aucune occurrence source de type False
```

Il exige au moins deux obligations conceptuellement distinctes :

1. **couverture** : aucune déclaration source pertinente n’est omise ;
2. **conservation des contre-exemples** : être une constante de type `False`
   est transporté du source vers l’objet présenté.

Le travail de minimisation doit ensuite :

1. prouver que ces obligations suffisent au transport de `no False` ;
2. tester séparément le retrait de chaque obligation ;
3. construire un séparateur lorsqu’un retrait autorise un faux transport ;
4. classer les autres déterminations étudiées — nom, position, préfixe, corps,
   dépendances et syntaxe — comme nécessaires, dérivables ou oubliables
   relativement à cette propriété précise ;
5. ne déclarer une détermination inutile que si un théorème de transport reste
   constructible sans elle.

La position et le préfixe peuvent être requis pour démontrer la couverture ou la
conservation dans l’implémentation réelle sans appartenir à l’énoncé minimal
abstrait. Cette différence entre donnée de preuve et dépendance logique du
résultat doit rester visible.

### Critère d’arrêt

Réduire cette gate à une étude documentaire si sa fermeture exige :

- une copie substantielle du code de ConLeche ;
- une dépendance technique du noyau scientifique envers ConLeche ;
- une réimplémentation générale de son frontend ;
- une modification importante des Cycles 1 ou 2.

## 11. Gate 6 — composition des statuts

Le résultat final juxtapose, sans les fusionner :

```text
certificat Lean de transport fidèle
+
rapport reproductible d’acceptation par ConLeche
```

Le certificat Lean peut établir une règle abstraite de transport :

```text
fidélité de la chaîne
+
propriété terminale précisément indexée
→
propriété source-relative précisément indexée
```

Il ne doit jamais contenir un champ `externalCheckerRecorded` présenté comme un
théorème si ce champ provient seulement de l’exécution du binaire.

La documentation rassemble les deux résultats et indique leur statut respectif.

## 12. Livrables finaux envisagés

Ne créer que ce qui devient effectivement nécessaire.

```text
ConstitutiveAlignment/
  VerificationTransport.lean

scripts/
  run_con_leche_audit.py

audit/
  CON_LECHE_VERIFIED_AUDIT.txt

docs/fr/
  audit_constitutif_con_leche.md

docs/en/
  constitutive_con_leche_audit.md
```

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

Éviter absolument :

```text
consistency-proven checker
fully verified end-to-end pipeline
proof of Lean consistency
proof that the whole ConLeche frontend preserves meaning
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
- README mis à jour seulement si l’audit est effectivement fermé.

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
Gate 0  compatibilité et gel
Gate 1  audit externe minimal
Gate 2  provenance exécutable du run
Gate 3  noyau formel spécialisé
Gate 4  séparateur constructif
Gate 4b alignement interne R → S
Gate 5a transformation ConLeche réelle
Gate 5b minimisation relative à no False
Gate 6  composition documentaire des statuts
```

Cet ordre empêche de construire une théorie volumineuse avant de savoir si
l’audit externe est effectivement réalisable avec le toolchain exact du dépôt.

## 16. Résultat minimal publiable

Le résultat minimal publiable comprend :

1. un run ConLeche `--verified --jobs=1` reproductible sur un export identifié ;
2. un lien opérationnel vérifié entre commit, export, hash et verdict ;
3. un séparateur Lean constructif entre acceptation terminale et fidélité amont ;
4. une reconstruction du contrat interne `R → S`, distincte de completeness et
   de la fidélité amont ;
5. une étude précisément bornée d’une transformation frontend réelle ;
6. une caractérisation suffisante et testée par séparateurs des déterminations
   nécessaires au transport de `no False` dans le cas étudié ;
7. une documentation bilingue distinguant toutes les portées.

Si la Gate 5 reste ouverte, les Gates 1 à 4 peuvent être publiées séparément à
condition de ne pas revendiquer une analyse constitutive du frontend réel.

## 17. Références externes à figer

- dépôt ConLeche : `https://github.com/leanprover/con-leche` ;
- contrat de ligne de commande et codes de sortie : `OVERVIEW.md`, section 0 ;
- théorème principal : `ConLeche/MainTheorem.lean` ;
- hypothèse en théorie des ensembles : `OVERVIEW.md`, section 7 ;
- frontière du frontend : `OVERVIEW.md`, section 9 ;
- format et exécutable d’export : `https://github.com/leanprover/lean4export`.

Le rapport final remplace les références de branche par les identifiants de
commit effectivement utilisés.
