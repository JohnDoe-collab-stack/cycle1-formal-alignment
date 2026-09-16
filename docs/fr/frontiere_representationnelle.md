# Frontière représentationnelle — exactitude locale et non-clôture diagonale

**Français** | [English](../en/representation_boundary.md)

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[alignement relatif](alignement_relatif.md) ·
[méthode](methode_roles_constitutifs_relationnels.md)

## Statut

Ce document décrit la branche autonome de frontière représentationnelle
implémentée dans :

```text
RepresentationBoundary/DiagonalizationKernel.lean
RepresentationBoundary/CircularStatusRepresentation.lean
```

Cette branche n'est pas une étape numérotée succédant à l'alignement. Le noyau
`DiagonalizationKernel` est indépendant de la théorie d'alignement et importe
seulement `Init`. Le module `CircularStatusRepresentation` fournit séparément
une application aux statuts circulaires déjà établis dans
`StrongPerimetralTurning`.

Quatre niveaux d'énoncés restent séparés :

1. **résultat vérifié mécaniquement** — déclaration démontrée dans Lean ;
2. **conséquence dérivée** — lecture mathématique directe des déclarations
   prouvées ;
3. **interprétation architecturale** — usage proposé du motif formel ;
4. **connexion gödelienne future** — non établie par le présent développement.

## 1. Place dans l'architecture

La théorie d'alignement dynamique et la frontière représentationnelle répondent
à deux questions différentes.

```text
alignement dynamique
  → cohérence entre transitions et réalisations
  → naturalité
  → composition / collage

frontière représentationnelle
  → représentation exacte d'un statut déterminé
  → diagonalisation de l'évaluateur
  → prédicat non représentable
  → absence de clôture représentationnelle globale
```

Aucun théorème de diagonalisation n'est requis pour prouver la naturalité,
la persistance ou le collage des alignements. Réciproquement, le théorème
`diagonalStatus_notRepresentable` n'utilise aucune notion d'alignement.

L'application aux statuts circulaires utilise seulement l'adéquation déjà
prouvée entre `CircularRefinement` et
`CircularSpecificationSatisfaction` afin de transporter une représentation
exacte entre deux prédicats propositionnellement équivalents.

## 2. Frontière de dépendance

```text
RepresentationBoundary.DiagonalizationKernel
  └── importe seulement Init

StrongPerimetralTurning
  ───────────────────────────────┐
                                 ├─→ RepresentationBoundary.CircularStatusRepresentation
RepresentationBoundary.DiagonalizationKernel
  ───────────────────────────────┘

RepresentationBoundary
  └── agrège les deux modules
```

Le noyau diagonal ne contient aucune définition de présentation circulaire,
d'histoire, de norme, de régime ou d'alignement.

## 3. Représentation exacte

La relation primitive est la représentation extensionnelle :

```lean
def Represents
    (eval : Code → Code → Prop)
    (program : Code)
    (predicate : Code → Prop) : Prop :=
  ∀ input, eval program input ↔ predicate input
```

Un programme représente donc un prédicat lorsqu'une ligne de l'évaluateur
coïncide exactement avec ce prédicat sur toute entrée.

La représentabilité interne est existentielle :

```lean
def InternallyRepresentable
    (eval : Code → Code → Prop)
    (predicate : Code → Prop) : Prop :=
  ∃ program, Represents eval program predicate
```

Aucune syntaxe, arithmétique, calculabilité ou théorie de la preuve n'est
supposée par ces définitions.

## 4. Statut diagonal construit

Le candidat diagonal est défini à partir de l'évaluateur lui-même :

```lean
def diagonalStatus (eval : Code → Code → Prop) : Code → Prop :=
  fun code => ¬ eval code code
```

Le théorème central est :

```lean
diagonalStatus_notRepresentable :
  ¬ InternallyRepresentable eval (diagonalStatus eval)
```

Si un programme `program` représentait `diagonalStatus eval`, la
spécialisation de la représentation à sa propre entrée donnerait :

```text
eval program program ↔ ¬ eval program program.
```

Les deux directions se réfutent alors constructivement. Aucun axiome diagonal
extérieur ni tiers exclu n'est requis.

## 5. Non-clôture représentationnelle globale

La propriété :

```lean
GlobalRepresentationClosure eval
```

affirme que chaque prédicat `Code → Prop` possède une ligne représentante
exacte dans `eval`.

Le théorème :

```lean
noGlobalRepresentationClosure :
  ¬ GlobalRepresentationClosure eval
```

est obtenu en appliquant une clôture supposée au prédicat
`diagonalStatus eval`.

Le vocabulaire « représentation » est volontaire : ce résultat ne constitue
pas une deuxième forme d'alignement et ne prétend pas qu'un système
opérationnel ne puisse pas poursuivre sa construction.

## 6. Point fixe local

`diagonalFixedPoint_ofRepresentable` formalise une observation de type
Lawvere. Si le prédicat :

```text
input ↦ operator (eval input input)
```

est représentable localement, alors il existe une proposition `p` telle que :

```text
p ↔ operator p.
```

Cette prémisse est locale. Elle ne suppose pas la clôture représentationnelle
globale, précisément réfutée par le théorème précédent.

Ce résultat n'est pas encore un théorème d'incomplétude de Gödel.

## 7. Sortie représentationnelle

`StatusRepresentationExit eval` contient :

```text
candidate : Code → Prop
outside   : ¬ InternallyRepresentable eval candidate
```

`diagonalStatusExit eval` fournit canoniquement une telle sortie avec
`diagonalStatus eval`.

Il ne s'agit pas d'un `AbstractSegmentedTurning.RegimeExit`. Les deux notions
portent sur des objets différents :

```text
RegimeExit
  → sortie d'un régime opérationnel sur un carrier

StatusRepresentationExit
  → sortie d'un régime de représentabilité sur les prédicats de codes
```

Aucun théorème ne les identifie.

## 8. Application aux statuts circulaires

Le module `CircularStatusRepresentation` observe seulement l'existence d'un
témoin :

```lean
HasStatus Status carrier := Nonempty (Status carrier)
```

Pour une présentation circulaire `P` :

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

`circularStatusAdequacy` établit :

```text
CircularRegimeStatus P H
  ↔
CircularSpecificationStatus P H
```

à partir des deux applications de témoins déjà prouvées. Cette équivalence ne
fusionne pas les types de témoins originaux.

## 9. Tiré en arrière vers les codes

Une fonction :

```lean
decode : Code → RootedGeneratedHistory P
```

tire les deux statuts vers des prédicats sur `Code`.
`codedCircularStatusAdequacy` conserve leur équivalence point par point.

Le théorème générique :

```lean
transportRepresentation
```

dit qu'une représentation exacte se transporte le long d'une équivalence
logique point par point.

Ainsi une représentation exacte du statut de régime fournit une représentation
exacte du statut normatif équivalent, et réciproquement.

## 10. Exactitude locale et frontière diagonale

La structure :

```lean
ExactCircularStatusRepresentation P Code
```

contient :

```text
decode
eval
program
representsRegime
```

Elle affirme uniquement qu'un statut circulaire déterminé est représenté
exactement.

Le théorème :

```lean
localExactRepresentation_hasDiagonalExit
```

réunit simultanément :

```text
représentation exacte du statut de régime choisi
+
représentation exacte du statut normatif équivalent
+
non-représentabilité du statut diagonal de l'évaluateur
```

Le théorème :

```lean
localExactRepresentation_notGloballyClosed
```

en déduit directement l'absence de `GlobalRepresentationClosure`.

C'est le résultat conceptuel principal de cette branche :

> **une représentation locale exacte de statuts déterminés peut coexister avec
> une frontière diagonale de la représentabilité globale.**

## 11. Modèle séparateur

`canonicalUnitCircularStatusRepresentation` construit une instance concrète sur
`Unit`.

Ce modèle montre que l'interface n'est pas vide. Il ne prétend pas fournir un
espace de codes non dégénéré ni un évaluateur universel.

`canonicalUnitCircularStatusRepresentation_hasDiagonalExit` vérifie
explicitement que même cette représentation exacte locale conserve une sortie
diagonale.

## 12. Relation à l'alignement

Le rapport avec l'alignement doit être formulé négativement et précisément :

```text
cohérence de l'alignement
  n'implique pas
clôture représentationnelle globale

frontière diagonale de représentation
  n'est pas nécessaire
à la preuve de l'alignement
```

La théorie de cohérence médiée actuellement expérimentée sur la branche
`research/mediated-transition-coherence` renforce encore cette séparation :
l'alignement, sa naturalité et son collage sont démontrés sans importer
`RepresentationBoundary`.

La frontière représentationnelle peut donc être conservée comme résultat
autonome sans lui attribuer un rôle fondateur dans l'alignement.

## 13. Relation à Gödel

Le noyau vérifié est un argument diagonal sémantique abstrait, proche des
arguments de Cantor/Lawvere.

Il ne fournit pas encore :

- une syntaxe de formules ;
- une substitution ou quotation ;
- une arithmétisation de la syntaxe ;
- un prédicat de prouvabilité ;
- une hypothèse formelle de cohérence ou d'effectivité ;
- une phrase de Gödel ;
- les théorèmes d'incomplétude.

Une instance gödelienne demanderait un développement syntaxique séparé.

## 14. Reproduction et audit

Depuis la racine :

```bash
lake clean
lake build
```

Les bibliothèques peuvent être construites séparément :

```bash
lake build Cycle1Alignment
lake build RepresentationBoundary
lake build AuditRegression
```

Les fichiers Lean de `RepresentationBoundary` se terminent par un bloc
`#print axioms` couvrant leurs déclarations publiques.

L'intégrité des sources est vérifiée par :

```bash
bash scripts/verify-manifest.sh
```

ou sous Windows :

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

## Conclusion

`RepresentationBoundary` est une branche autonome de limite représentationnelle,
et non une étape de l'alignement. Elle formalise la coexistence entre exactitude
locale de représentation et impossibilité d'une clôture représentationnelle
globale pour un évaluateur de type `Code → Code → Prop`.

Cette reformulation conserve le résultat diagonal tout en supprimant une
fausse dépendance narrative avec la théorie d'alignement.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit par des modèles
> de la série ChatGPT d'OpenAI, sous direction humaine. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
