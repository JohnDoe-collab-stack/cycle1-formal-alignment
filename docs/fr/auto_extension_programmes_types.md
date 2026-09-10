# Auto-extension constitutive de programmes typés

[English](../en/typed_program_self_extension.md) | **Français**

Navigation : [architecture neuronale](alignement_constitutif_transformers.md) ·
[fondements structurels](fondements_structurels.md) ·
[alignement relatif](alignement_relatif.md)

## 1. Résultat construit

Le dépôt construit un témoin fini dans lequel une abstraction nouvelle modifie
positivement le corpus qui détermine la construction suivante :

```text
T₀
→ frontière typée calculée depuis T₀
→ proposition, certification et incorporation de C₀
→ T₁ effectivement produit
→ même règle de frontière appliquée à T₁
→ obligation nouvelle δ₁
→ seconde proposition, certification et incorporation
→ T₂
```

Ni la fonction de frontière ni `typedStep` ne reçoit un rang de cycle. Le
second appel consomme le `T₁` produit par le premier ; il ne lit pas une fixture
nommée « deuxième état ».

Ce résultat raccorde directement le noyau du Cycle 1 : construction, admission,
norme et adéquation restent des objets distincts. L’apprentissage ne crée pas
la norme et la proposition ne vaut pas encore incorporation.

## 2. Domaine total et identité de formation

`TypedProgramDomain.lean` définit :

- deux types de programme finis, `bit` et `pair` ;
- un langage intrinsèquement typé avec identité, négation, duplication,
  première projection et composition ;
- une sémantique totale `Program.evaluate` ;
- une formation syntaxique conservée séparément du comportement ;
- une abstraction existentielle positive portant interface et programme typé ;
- un corpus fini, un régime, une norme déclarée indépendamment et les deux
  transformations d’adéquation.

L’égalité extensionnelle n’efface pas la formation. La double négation calcule
la même valeur que l’identité sur tout booléen, mais sa formation est
constructivement distincte. À l’inverse, une tentative de composer une sortie
`pair` avec la négation `bit → bit` retourne `none` : le typage n’est jamais
réparé après coup.

La frontière énumère exhaustivement les paires du corpus dans un ordre fixe,
construit les seules compositions typées et retourne soit la première formation
absente avec ses témoins de présence et de fraîcheur, soit un certificat de
saturation fini.

## 3. Deux passages par le même opérateur

L’instance canonique part du corpus contenant seulement la négation :

```text
T₀ = [not]
frontière(T₀) = not ∘ not
T₁ = [not, not ∘ not]
frontière(T₁) = not ∘ (not ∘ not)
T₂ = [not, not ∘ not, not ∘ (not ∘ not)]
```

Le même `typedStep` réalise les deux transitions. `TypedStep` est un type de
témoin positif, et `secondHistory` compose les transitions dans l’histoire
proof-relevant déjà employée par le socle structurel.

Les ancrages principaux sont :

| Obligation | Ancrage Lean |
| --- | --- |
| première formation fraîche | `firstCertifiedAbstraction_isFresh` |
| première frontière | `firstFrontier_isDoubleNegate` |
| seconde frontière | `secondFrontier_isTripleNegate` |
| reconstruction de `T₁` | `firstStep_reconstructsCorpus` |
| consommation exacte de `T₁` | `secondStep_consumesFirstSuccessor` |
| divergence sans incorporation | `firstIncorporation_changesSecondObligation` |
| agrégation finale | `compactTypedSelfExtension` |

Le premier contrefactuel conserve la capacité acquise mais retire seulement
l’incorporation de `C₀` : la frontière reste alors la double négation au lieu de
devenir la triple négation. Le second conserve `T₁` mais restaure la capacité
antérieure au second apprentissage : aucune seconde proposition n’est produite.
Les deux causalités sont donc séparées.

## 4. Raccord au producteur transformer

`programCore` est une instance locale de `TransformerCore`. Sa proposition est
un objet positif `CertifiedProgramAbstraction`, non un booléen décodé par une
table de cas. Le producteur calcule la frontière depuis le corpus de sa vue et
ne propose le candidat que lorsque la capacité compositionnelle acquise suffit.
L’élaborateur total rejette l’absence de proposition ou conserve exactement
l’abstraction proposée.

La première capacité acquise est celle portée par `T₁`. Elle devient la capacité
entrante du second passage. Le second apprentissage produit exactement la
capacité consommée par la seconde dynamique. `StrictFreshProbeCausality`
construit sur une même vue le rejet parent, le changement de prédiction, la
consommation exacte, le changement de proposition et la succession apprise.

## 5. Sonde générée et raffinement exact

`GeneratedFreshProbeProtocol` porte ensemble le descripteur scellé, la graine
réservée, le générateur total, sa sortie et l’égalité avec la sonde du protocole
fixe sous-jacent. Pour l’instance finie, la formation de triple négation est
constructivement absente du corpus d’entraînement, qui ne contient que la
double négation.

La frontière exécutable typée est reliée à une trace canonique par
`TypedTraceRefinement`. L’égalité porte sur toute la trace discrète. Elle donne
notamment la consommation exacte de la prédiction et l’identité entre statut du
certificat et effet gouverné. Une proposition réécrite ou un corpus cible privé
de la première incorporation ne possède aucun tel raffinement.

## 6. Protocole exécutable séparé

`experiment/typed_program/` reproduit la même chaîne dans un journal JSON sans
être lu par Lean. Le worker est sans état :

- l’appel d’apprentissage reçoit uniquement la vue d’entraînement, la capacité
  entrante et les bornes publiques ;
- l’appel de mesure reçoit l’entrée de sonde, mais aucune cible, et ne peut pas
  mettre l’état à jour ;
- la réponse attendue est recalculée par une sémantique totale indépendante ;
- chaque requête exacte est inscrite dans le journal primaire.

Après scellement du descripteur, une graine préengagée engendre une séquence de
bits déterministe. Le ledger cumulatif réserve les signatures normalisées des
données d’entraînement et des sondes ; toute collision arrête le run sans
retirage. Le normaliseur efface uniquement les adresses techniques : un
renommage cohérent conserve la clé et la sonde, sans rendre fraîche une
exposition antérieure.

Le smoke test de développement et douze mutations négatives passent. Le run
confirmatoire reste volontairement absent : le programme le refuse tant que
les sources n’ont pas été gelées par un commit propre. La Gate N ne sera donc
déclarée fermée qu’après ce gel, un run confirmatoire unique dans un chemin neuf
et sa vérification en lecture seule.

## 7. Portée exacte

La partie Lean établit constructivement, dans ce langage fini, l’existence de
deux transitions liées, la dépendance de la seconde frontière à la première
incorporation, la dépendance de la seconde proposition à la capacité acquise,
la fraîcheur de la sonde formelle et le raffinement exact des traces discrètes.

Elle ne démontre ni synthèse générale de programmes, ni apprentissage de
primitives depuis rien, ni autonomie non bornée, ni résultat empirique sur un
transformer entraîné à grande échelle. Ces absences ne diminuent pas le témoin :
elles en fixent la portée vérifiée.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d’OpenAI, sous direction humaine et au cours
> d’interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
