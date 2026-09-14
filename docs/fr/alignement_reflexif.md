# Cycle 2 — Alignement réflexif et non-clôture diagonale

**Français** | [English](../en/reflective_alignment.md)

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[Cycle 1 — alignement relatif](alignement_relatif.md) ·
[méthode](methode_roles_constitutifs_relationnels.md)

## Statut

Ce document décrit l'extension autonome du cycle 2 implémentée dans
`Cycle2/DiagonalizationKernel.lean` et `Cycle2/ReflectiveAlignment.lean`.
Chaque déclaration Lean nommée ci-dessous est compilée avec Lean 4.33.1 et
couverte par l'audit final `#print axioms` du dépôt.

Quatre niveaux d'énoncés sont maintenus séparés:

1. **résultat vérifié mécaniquement** — déclaration démontrée dans Lean;
2. **conséquence dérivée** — lecture mathématique directe des déclarations prouvées;
3. **interprétation architecturale** — usage proposé du motif formel;
4. **connexion gödelienne future** — non établie par ce cycle.

## Place dans l'architecture générale

Le Cycle 2 n'est pas une branche indépendante raccordée directement au socle
structurel. Il part de l'adéquation déjà établie par les deux applications de
témoins du Cycle 1, observe cette adéquation au niveau propositionnel par
`Nonempty`, puis seulement la transporte dans la couche de représentation :

```text
applications de témoins du Cycle 1
  → adéquation relative exacte
  → équivalence des statuts par `Nonempty`
  → tiré en arrière vers les codes
  → transport de représentation exacte
  + diagonalisation de l'évaluateur
  → représentation exacte déterminée avec non-clôture globale
```

La continuation opérationnelle `oneStepAfterPerimeter` appartient à une autre
branche située après l'adéquation du Cycle 1. Elle n'est pas une entrée de la
preuve diagonale.

## 1. Objet

Le cycle 1 sépare construction, réalisation fidèle, admission opérationnelle et
satisfaction d'une norme indépendante. Le cycle 2 pose une question différente:
un évaluateur peut-il représenter intérieurement tous les statuts propositionnels
sur son propre espace de codes?

La réponse est constructivement négative. Étant donné

```lean
eval : Code → Code → Prop
```

le développement construit un prédicat à partir de `eval` lui-même et démontre
qu'aucune ligne de `eval` ne le représente exactement. Il s'agit d'une frontière
au niveau de la représentation, non d'une frontière opérationnelle entre
histoires.

## 2. Frontière de dépendance

```text
Cycle2.DiagonalizationKernel ── importe seulement Init ──┐
                                                         ├─→ Cycle2.ReflectiveAlignment
StrongPerimetralTurning ─────────────────────────────────┘             │
                                                                       ▼
                                                                     Cycle2
```

`Cycle2.DiagonalizationKernel` ne contient aucune définition de présentation
circulaire, d'histoire, de norme, de régime ou d'alignement. Tout contact avec
le cycle 1 est confiné à `Cycle2.ReflectiveAlignment`. Réciproquement, aucun
module du cycle 1 n'importe le cycle 2.

## 3. Représentation exacte

La relation primitive est la représentation extensionnelle:

```lean
def Represents
    (eval : Code → Code → Prop)
    (program : Code)
    (predicate : Code → Prop) : Prop :=
  ∀ input, eval program input ↔ predicate input
```

Un code représente donc un prédicat lorsqu'une ligne de l'évaluateur coïncide
avec ce prédicat sur toute entrée. La représentabilité interne est existentielle:

```lean
def InternallyRepresentable
    (eval : Code → Code → Prop)
    (predicate : Code → Prop) : Prop :=
  ∃ program, Represents eval program predicate
```

Aucune syntaxe, calculabilité, arithmétique, théorie de la preuve ou sémantique
intentionnelle n'est supposée à ce niveau.

## 4. Statut diagonal construit

Le candidat est défini, non postulé:

```lean
def diagonalStatus (eval : Code → Code → Prop) : Code → Prop :=
  fun code => ¬ eval code code
```

Le théorème central est:

```lean
diagonalStatus_notRepresentable :
  ¬ InternallyRepresentable eval (diagonalStatus eval)
```

Supposons qu'un code `program` représente `diagonalStatus eval`. La
spécialisation de l'équivalence de représentation à `program` donne

```text
eval program program ↔ ¬ eval program program.
```

Chaque direction réfute alors l'autre constructivement. La preuve n'utilise ni
tiers exclu ni axiome diagonal externe.

## 5. Non-clôture globale

La clôture réflexive globale affirme que chaque prédicat sur `Code` possède une
ligne représentante exacte:

```lean
def GlobalReflectiveClosure (eval : Code → Code → Prop) : Prop :=
  ∀ predicate, InternallyRepresentable eval predicate
```

Le théorème

```lean
noGlobalReflectiveClosure : ¬ GlobalReflectiveClosure eval
```

est dérivé en appliquant la clôture proposée à `diagonalStatus eval`, puis en
invoquant `diagonalStatus_notRepresentable`. Le témoin de l'échec est donc
explicite et reste lié à l'évaluateur auquel il échappe.

`diagonalFixedPoint` condense également l'observation correspondante de type
Lawvere: la représentation globale fournirait un point fixe à tout opérateur
`Prop → Prop`. Le choix de la négation explique pourquoi cette prémisse globale
ne peut tenir. Ce théorème n'ajoute aucun résultat de cohérence ou
d'incomplétude; sa prémisse est précisément la clôture déjà réfutée ci-dessus.

## 6. Sortie au niveau de la représentation

`StatusRepresentationExit eval` enregistre:

```text
candidate : Code → Prop
outside   : ¬ InternallyRepresentable eval candidate
```

`diagonalStatusExit eval` instancie cette structure avec le prédicat diagonal
construit. Il s'agit de l'analogue représentationnel, pour le cycle 2, d'un
certificat de sortie. Ce n'est délibérément pas un
`AbstractSegmentedTurning.RegimeExit`: les deux structures classent des objets
différents sous des régimes différents.

## 7. Lecture propositionnelle du cycle 1

Les statuts du cycle 1 sont des familles porteuses de témoins. Le cycle 2 observe
seulement l'existence d'un témoin:

```lean
HasStatus Status carrier := Nonempty (Status carrier)
```

Pour une présentation circulaire `P` et une histoire `history`, il définit:

```text
CircularRegimeStatus        := Nonempty (CircularRefinement P history)
CircularSpecificationStatus := Nonempty
  (CircularSpecificationSatisfaction P history)
```

Le théorème `circularStatusAdequacy` démontre leur équivalence en utilisant dans
les deux sens les applications de soundness et de complétude du cycle 1.
`Nonempty` n'est qu'une observation propositionnelle; il ne remplace ni
n'identifie les types de témoins originaux.

## 8. Tiré en arrière vers les codes et transport

Une fonction de décodage

```lean
decode : Code → RootedGeneratedHistory P
```

tire chaque statut d'histoire en arrière vers un prédicat sur les codes. Le
théorème `codedCircularStatusAdequacy` démontre l'équivalence point par point des
statuts de régime et de spécification ainsi obtenus.

`transportRepresentation` établit ensuite une règle générale: la représentation
exacte se transporte le long d'une équivalence logique point par point. Par
conséquent:

```text
représentation du statut du régime circulaire
  ↔ représentation du statut de la spécification circulaire.
```

Ce transport utilise l'adéquation normative déjà démontrée. Il ne définit pas
la norme à partir du régime et ne suppose aucune représentabilité universelle.

## 9. Représentation exacte de statuts déterminés et non-clôture globale

`ReflectiveCircularStatusView P Code` contient un décodeur, un évaluateur, un
programme et une preuve que ce programme représente exactement le statut tiré
en arrière du régime circulaire. L'adéquation fournit la représentation exacte
du statut de spécification par le même programme.

Le théorème `exactCircularStatusRepresentation_hasDiagonalOutside` réunit trois
faits simultanés:

```text
le statut de régime choisi est représenté exactement
le statut normatif équivalent est représenté exactement
le statut diagonal de l'évaluateur n'est pas représentable intérieurement
```

`exactCircularStatusRepresentation_notGloballyClosed` énonce l'échec
correspondant de la clôture réflexive globale. La représentation exacte de ces
statuts déterminés et l'adéquation normative coexistent donc avec un extérieur
représentationnel précisément localisé.

Le modèle fermé sur `Unit`, `canonicalUnitCircularStatusView`, vérifie que cette
interface est habitée: un statut circulaire particulier peut être représenté
par un évaluateur constant sans transformer cet évaluateur en évaluateur
universel.
Il s'agit actuellement de la seule vue réflexive de statuts construite dans le
dépôt. Elle établit l'habitation de l'interface, non l'existence d'un espace de
codes non dégénéré ou d'un évaluateur non constant.

## 10. Deux sorties non identifiées

Les cycles 1 et 2 construisent des frontières distinctes:

| Niveau | Candidat | Régime | Perte certifiée |
|---|---|---|---|
| opérationnel | `oneStepAfterPerimeter P` | `CircularRefinement P` | admission opérationnelle et satisfaction normative |
| représentationnel | `diagonalStatus eval` | `InternallyRepresentable eval` | représentation interne exacte |

Le premier candidat est une histoire qui reste constructible et qui, comme
toute histoire générée enracinée de ce développement, admet une réalisation
concrète exacte. Le second est un prédicat sur les codes construit à partir d'un
évaluateur. Aucun théorème du dépôt ne convertit une sortie dans l'autre, et
aucune conversion de ce type n'est supposée.

## 11. Relation à Gödel

La preuve vérifiée est un argument diagonal sémantique abstrait, proche de la
non-surjectivité de Cantor/Lawvere. Elle capture le fait architectural qu'un
évaluateur ne peut énumérer extensionnellement tous les prédicats sur son propre
espace de codes.

Elle ne fournit **pas** encore:

- une syntaxe de formules;
- une substitution ou une quotation;
- une arithmétisation de la syntaxe;
- un prédicat de prouvabilité;
- une hypothèse formelle de cohérence ou d'effectivité;
- une phrase de Gödel;
- l'un ou l'autre théorème d'incomplétude.

Une instance gödelienne formelle demanderait ces composants dans un
développement syntaxique séparé. Le résultat présent peut lui servir de noyau
diagonal abstrait, mais n'est pas lui-même cette instance.

## 12. Reproduction et audit

Depuis la racine du dépôt:

```bash
lake clean
lake build
```

Pour construire séparément les deux bibliothèques:

```bash
lake build Cycle1Alignment
lake build Cycle2ReflectiveExtension
```

Les fichiers sources du cycle 2 se terminent par des `#print axioms` couvrant
leurs 28 déclarations explicites de premier niveau. La compilation complète
exécute 454 commandes `#print axioms` portant sur 453 déclarations distinctes ;
une déclaration est auditée une seconde fois par l'agrégateur `Cycle2.lean`.
Chaque rapport affirme que la déclaration nommée ne dépend d'aucun axiome.
L'intégrité des sources se vérifie avec:

```bash
bash scripts/verify-manifest.sh
```

ou:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

## 13. Conclusion stabilisée

Le cycle 2 vérifie mécaniquement un noyau constructif autonome de non-clôture
réflexive. Il construit le statut qui échappe à la représentation, démontre sa
non-représentabilité, transporte l'adéquation normative du Cycle 1 à travers la
représentation exacte de statuts déterminés et établit que cette exactitude ne
s'effondre pas en clôture globale. Sa portée formelle reste volontairement plus
étroite que l'incomplétude gödelienne et ne fusionne pas la sortie opérationnelle
du cycle 1 avec la sortie représentationnelle du cycle 2.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l'origine de l'essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d'OpenAI, sous direction humaine et au cours
> d'interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
