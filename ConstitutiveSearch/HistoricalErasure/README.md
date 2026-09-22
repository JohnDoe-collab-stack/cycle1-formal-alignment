# Amplification historique non inversible

Extension de `528ba7a8c95cb7626655597cab511c221e23364a`, sur la branche
`research/noninvertible-historical-amplification`.

## Objet et ordre de lecture

Le développement formalise un témoin de réduction de largeur de référence par
des transports totaux préservant séparément l'acceptation, non injectifs et
conditionnés par la sortie de l'étape précédente. Il réutilise les interfaces
`SearchSystem` et `AcceptingContinuationTransport` du dépôt. Les anciennes
fondations, la récursion intégrée `NPAndOrP` et son manifeste ne sont pas modifiés.

Lire dans cet ordre :

1. `Local.lean` : sémantique séparée, collision de continuations acceptées,
   impossibilité avec garde fausse, recherche exhaustive des 16 tables de
   fonctions booléennes locales et certification de leurs 8 entrées.
2. `Chain.lean` : étapes produites, transmission de la garde lue sur la sortie,
   récursion à longueur quelconque, préservation du noyau, transport vers
   l'histoire retenue et viabilité de chaque histoire de référence.
3. `Amplification.lean` : énumération sans doublons des histoires de référence,
   largeur exponentielle, équivalence de viabilité et domination asymptotique
   du compteur défini par l'exécution.
4. `Regression.lean` : preuves closes et vérifications exécutables, y compris
   échec de découverte, rejet d'un certificat incorrect et profondeurs 0 à 64.

## Famille représentée

Une cellule possède une décision `d`, un contenu modifiable `y` et un bit de
noyau `z`. Sa garde sortante est `d || !(y == z)`. Pour une chaîne, les contraintes
sont exactement :

```text
G(z_1,...,z_n)
and for every i: d_i = true -> y_i = z_i
and for every i > 1: d_i = true -> d_(i-1) = true or y_(i-1) != z_(i-1).
```

La garde initiale vaut vrai. `G` est un prédicat fourni, conservé mais jamais
évalué par la découverte ou l'exécution. Aucune hypothèse de décidabilité ou de
satisfiabilité de `G` n'est nécessaire pour construire le transport. Un témoin
satisfaisant `G` est requis uniquement pour affirmer que toutes les branches
sont effectivement viables.

Le transport local cherche une table calculant le nouveau `y` à partir de
`(y,z)`, avec `d` fixé à vrai. Les seize fonctions possibles sont énumérées ;
la bonne table n'est pas passée comme argument à la découverte. La vérification
porte sur les huit continuations structurelles `(y,z,nextDecision)`. Un résultat
positif produit une table accompagnée de sa preuve de correction. La table
valide est ensuite caractérisée par un théorème, et non fournie à la recherche.

Avec garde vraie, la sixième tentative réussit après cinq échecs. Avec garde
fausse, les seize tentatives échouent. Il est en outre démontré qu'aucun
transport préservant l'acceptation n'existe dans le système local bloqué : la
source possède une continuation acceptée, tandis que la cible n'en possède
aucune. Cette obstruction concerne le système local dont la garde reste fixée,
non toutes les transformations possibles d'une chaîne entière.

L'application valide met `d` à vrai et, sur la branche fausse, remplace `y` par
`z`. Deux sources acceptées distinctes peuvent ainsi donner la même sortie.
Aucun inverse gauche n'existe pour cette application. Les histoires source et
cible restent des états distincts ; la collision est celle des continuations.

Chaque `Stage` retient la découverte réellement obtenue, son certificat, la
revérification et la cellule produite. Le constructeur `Execution.step` indexe
sa suite par `stage.nextGuard`, une lecture de cette cellule produite. Le
théorème disant que cette garde vaut vrai est séparé de cette construction.

## Énoncés vérifiables

Les principaux noms exportés sont dans `ConstitutiveSearch.HistoricalErasure` :

- `acceptedCollision`, `resetNoLeftInverse`, `blockedTransportImpossible` ;
- `checkTable_sound`, `checkTable_unique`, `payloadTables_complete` ;
- `discoveredCertificate_from_run` ;
- `Execution.output_cores`, `Execution.history_is_output` ;
- `Execution.preserves_acceptance`, `normalizingTransport` ;
- `every_branch_viable`, `all_reference_branches_viable` ;
- `branches_length`, `branches_nodup`, `reference_viable_iff_retained` ;
- `executed_width_cost`, `amplification_unbounded`, `amplificationCertificate`.

Pour `n = cells.length`, la largeur du déploiement complet de référence vaut
`2^n`, et une seule histoire est conservée. Cette énumération exponentielle
n'est pas appelée par `execute`. La liste des tables produites a longueur `n`.

Le compteur déclaré `work` totalise les lignes vérifiées pendant la découverte,
les lignes de revérification et quatre unités fixes par étape. Les égalités
prouvées sont :

```text
(execute cells).attempts = 6 * cells.length
(execute cells).work = 60 * cells.length.
```

Le résultat asymptotique est un théorème quantifié, pas une extrapolation de
mesures :

```text
forall K, exists threshold, forall cells,
  threshold <= cells.length ->
  K * (execute cells).work < (branches cells.length).length - 1.
```

Le seuil explicite `60*K + 5` suffit.

## Représentation et portée du coût

Cette implémentation Lean reçoit une chaîne de cellules **déjà structurée et
ordonnée**. Elle recherche les fonctions locales, mais ne reconstruit pas
l'appariement des variables ni l'ordre des blocs à partir d'une CNF sans
structure auxiliaire. Elle n'est donc pas une vérification du parseur et du
synthétiseur CNF Python précédemment expérimentés. Leur coût cubique et le
compteur linéaire présent ne portent pas sur les mêmes opérations d'entrée.

`60*n` est une comptabilité explicite au niveau du code source, pas un théorème
sur le temps machine. Le développement ne prétend ni résoudre le noyau `G`, ni
énumérer gratuitement `2^n` branches, ni prouver une borne inférieure sur les
autres algorithmes. Il ne formule aucun résultat sur les classes classiques
P/NP et aucune revendication bibliographique de priorité.

## Reproduction complète

Depuis un clone de cette branche disposant de la chaîne d'outils indiquée dans
`lean-toolchain` :

```bash
bash scripts/verify-historical-erasure.sh
```

Ce script échoue si l'un des quatre modules manque. Il construit le projet
original et `AuditRegression`, compile chaque nouveau module en `.olean` et en
C, contrôle les sorties `#print axioms`, exécute les régressions puis lance les
vérifications constructives et le manifeste du dépôt. Les journaux, le SHA
exact et la version de Lean sont conservés dans
`/tmp/historical-erasure-verification` par défaut.

La compilation et l'exécution doivent être constatées sur le **même commit**.
Le marqueur final de réussite est :

```text
HISTORICAL_ERASURE_VERIFIED commit=<SHA>
```

Le workflow `Historical erasure verification` lance ce script pour les pushes
sur la branche. Sa réussite est distincte de celle du workflow d'origine, qui
ne suffit pas à vérifier ces nouveaux modules.
