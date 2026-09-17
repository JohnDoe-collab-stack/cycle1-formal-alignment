# Fondements structurels — détermination constitutive, alignement relatif et frontière représentationnelle

[English](README.md) | **Français**

> **Ce dépôt développe et vérifie en Lean un cadre constructif permettant de suivre une même détermination constitutive à travers des couches distinctes sans fusionner ces couches entre elles.**
>
> Les objets sont individués avant d'être lus, leurs rôles sont déterminés par les relations qui les constituent, les dépendances sont éprouvées sur des carriers affaiblis, puis seules les déterminations dont la conservation a été démontrée sont reconstruites et transportées.
>
> Dans l'instance circulaire, cela permet de construire une continuation opérationnelle exacte dont le statut change sans perte de constitution, d'identifier son occurrence résiduelle à l'identité fraîche de l'alignement constitutif, puis de démontrer que cette identité persiste de manière cohérente à travers toute extension finie fournie et entre des réalisations exactes distinctes.
>
> Une branche séparée de frontière représentationnelle établit un résultat constructif de non-représentabilité diagonale. Elle ne produit pas la sortie opérationnelle et n'est pas utilisée pour justifier la persistance constitutive.

---

## Présentation théorique longue

La présentation théorique détaillée en français est maintenue séparément :

- **[Présentation longue — théorie constitutive de la détermination relationnelle](PRESENTATION_LONGUE.md)**

---

## Positionnement scientifique

Ce projet étudie comment une structure relationnelle peut d'abord constituer canoniquement son propre domaine interne, puis déterminer ce qui apparaît comme nouveau lorsque la même construction se prolonge au-delà de ce domaine. Dans l'instance circulaire formalisée ici, cette progression relie reconstruction du périmètre, détermination résiduelle, frontière de régime, naissance d'une identité fraîche et persistance cohérente de cette identité. La contribution proposée ne réside donc pas dans une notion isolée de clôture, de totalité ou de transport, mais dans la construction formelle de cette chaîne de dépendances.

Voir [POSITIONNEMENT_SCIENTIFIQUE.md](POSITIONNEMENT_SCIENTIFIQUE.md) pour le positionnement comparatif détaillé.

---

## 1. Unité théorique

L'unité théorique de ce projet n'est ni un module particulier ni un théorème final.

Elle réside dans la continuité démontrée d'une **même détermination** à travers plusieurs couches distinctes et interdépendantes.

```text
constitution
    ↓
occurrence individuée
    ↓
détermination structurelle
    ↓
extension / continuation
    ↓
changement de statut
    ↓
réalisation exacte
    ↓
persistance finie
    ↓
transport entre réalisations
    ↓
lecture
```

Ces couches sont reliées, mais elles ne sont pas identifiées.

Le projet conserve délibérément des distinctions comme :

```text
occurrence ≠ lecture

constitution ≠ réalisation

réalisation ≠ admission

admission ≠ satisfaction d'une norme indépendante

identité ≠ égalité des valeurs observées

sortie opérationnelle ≠ sortie représentationnelle
```

La question centrale n'est donc pas seulement :

> Quelle valeur possède un objet ?

mais d'abord :

> Qu'est-ce qui fait de cette occurrence cette occurrence, quelles relations constituent son rôle, et que faut-il préserver pour démontrer que la même détermination persiste à travers une transformation ?

Les rôles sont établis avant leurs représentations, transportés sans fusionner les couches, puis seulement rendus disponibles à des lectures indépendantes.

---

## 2. Méthode des rôles constitutifs relationnels

Le développement suit une discipline méthodologique extraite de l'instance circulaire.

Sa forme condensée est :

```text
individuer
→ relier
→ séparer
→ reconstruire
→ transporter
→ diagnostiquer
```

### Individuer

Les occurrences sont construites comme objets proof-relevant avant qu'une valeur leur soit attribuée.

Deux occurrences ne sont pas identifiées simplement parce qu'une lecture leur donne la même valeur.

### Relier

Une occurrence est déterminée par les relations structurelles dans lesquelles elle intervient :

```text
formation
provenance
source
cible
position
succession
composition
accord avec un rôle structurel
```

Un rôle constitutif relationnel n'est donc pas une simple étiquette ajoutée à un objet déjà donné. Il décrit comment l'occurrence est déterminée au sein de la construction.

### Séparer

Lorsqu'il n'est pas clair qu'une propriété doit être primitive, la méthode affaiblit le carrier tout en conservant les couches déjà établies.

Elle construit ensuite des modèles séparateurs.

Par exemple, le développement établit sur des carriers affaiblis que :

```text
accord local exact + injectivité
⇏ ordre structurel
```

et :

```text
accord local exact
+ injectivité
+ ordre préservé
+ position intermédiaire
⇏ participation à une composition constitutive
```

Un contre-modèle sert à établir une frontière de dépendance, pas seulement à l'illustrer.

### Reconstruire

Après la séparation, la structure réelle de construction est réintroduite.

Des propriétés comme la précédence et l'adjacence deviennent alors dérivables de l'accord exact combiné à la composabilité dépendante des histoires réelles.

La méthode cherche donc à minimiser les primitives sans appauvrir l'objet.

Une propriété ne doit pas rester primitive lorsqu'elle peut déjà être reconstruite à partir d'une structure constitutive plus fondamentale.

### Transporter

Un changement de représentation n'est accepté comme fidèle que lorsque les occurrences pertinentes restent exactement récupérables.

Une interprétation fidèle d'une histoire fournit des applications aller-retour sur les occurrences, des lois ponctuelles d'aller-retour et des accords structurels.

L'identité n'est pas déduite d'une égalité de valeurs finales, d'une égalité de cardinalités ou d'un score de similarité.

### Diagnostiquer

Ce n'est qu'après avoir établi la constitution et la conservation que les statuts opérationnels et normatifs sont comparés.

La méthode maintient distincts :

```text
Construction(H)

RealisationFidele(A, H)

Regime(H)

Norme(H)
```

Une sortie typée conserve le candidat et les preuves positives de ce qui reste valide tout en portant la preuve de la propriété exacte qui échoue.

Le résultat est donc un **diagnostic structurel**, pas seulement une classification négative.

Le développement méthodologique complet se trouve dans :

[`docs/fr/methode_roles_constitutifs_relationnels.md`](docs/fr/methode_roles_constitutifs_relationnels.md).

---

## 3. Ordre de dépendance

L'ordre de construction visé est :

```text
présentation
→ formations possibles
→ occurrences individuées
→ accord exact rôle/occurrence
→ succession et composition
→ invariants structurels
→ réalisations concrètes fidèles
→ lectures dérivées et invariants numériques
→ norme indépendante et régime opérationnel définis séparément
→ adéquation
→ diagnostic
```

Cet ordre est méthodologique et non l'ordre chronologique des fichiers sources.

Son objectif est d'empêcher qu'une couche ultérieure définisse silencieusement une couche antérieure.

Par exemple :

- une lecture ne doit pas définir l'identité d'une occurrence ;
- un invariant numérique ne doit pas définir la structure dont il est l'invariant ;
- un régime ne doit pas définir la norme indépendante relativement à laquelle son adéquation est évaluée ;
- une représentation ne doit pas constituer rétroactivement l'objet qu'elle représente.

---

## 4. Fondation constitutive

Une `CircularPresentation` détermine les données et les règles de formation de l'instance circulaire.

À partir d'elle, le développement construit :

```text
PositiveConstitution
        ↓
GeneratedStep
        ↓
History
        ↓
RootedGeneratedHistory
        ↓
History.Occurrence
```

Les occurrences sont donc générées dans une histoire dépendamment typée plutôt qu'extraites d'une séquence externe de valeurs.

Le déploiement canonique du périmètre est :

```text
perimeterDeployment P
```

et le générateur reste applicable à sa frontière, ce qui produit :

```text
oneStepAfterPerimeter P
```

comme véritable continuation constitutive stricte.

---

## 5. L'exactitude locale reconstruit la structure globale

Pour une présentation circulaire `P` et une histoire générée enracinée `H`, une réalisation locale exacte fournit une occurrence de `H` pour chaque position non fermante du périmètre, avec un accord structurel exact.

Le théorème central de reconstruction est :

```text
ExactNonClosingRealization P H
→
PerimeterExtension P H
```

implémenté par :

```lean
ExactNonClosingRealization.toPerimeterExtension
```

Le périmètre canonique est ainsi reconstruit comme facteur initial exact de l'histoire.

Cela ne signifie **pas** que l'histoire est épuisée par le périmètre.

La distinction est essentielle :

```text
chaque exigence structurelle possède un témoin exact
≠
chaque occurrence appartient à la famille d'exigences couverte
```

L'ouverture laissée par cette distinction permet précisément de construire une continuation supplémentaire sans invalider la réalisation du périmètre déjà établie.

L'injectivité est dérivée de l'accord exact plutôt que postulée séparément. La précédence et l'adjacence sont testées sur des carriers affaiblis puis reconstruites sur le carrier réel des histoires.

---

## 6. Détermination résiduelle

Une extension positive introduit une nouvelle partie dont l'occurrence résiduelle peut être déterminée constructivement.

L'analyse résiduelle est factorisée de sorte que la détermination effective ne dépende que d'un noyau résiduel plus faible, plutôt que de l'intégralité du contrat historique de réalisation interne exacte.

Schématiquement :

```text
contrat historique riche
        ↓
noyau de détermination résiduelle
        +
partie nouvelle positive
        ↓
occurrence résiduelle unique
```

L'affaiblissement est réel dans la classe générale : `SegmentedResidualRoleStrictness.lean` contient des séparateurs positifs où la détermination résiduelle réussit encore alors que la réalisation interne exacte plus riche, ou sa reconstruction compatible, n'est pas disponible.

Réciproquement, le développement caractérise les conditions sous lesquelles la structure interne exacte plus riche peut être reconstruite.

La factorisation sépare donc :

```text
détermination exacte du nouveau résidu
≠
individuation exacte et persistance de toutes les anciennes occurrences
```

Le chemin de conservation vers le producteur circulaire réel est explicite. Les constructions faible et riche sélectionnent la même occurrence positive, ce qu'exposent notamment :

```lean
SegmentedResidualRole.positiveExtension_result_occurrence

StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_weak

StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_consumedTurning
```

La dérivation affaiblie n'est donc pas une construction résiduelle concurrente. Elle factorise celle qu'utilise déjà le producteur circulaire.

---

## 7. Turning opérationnel et changement de statut

L'instance circulaire réalise le mécanisme abstrait de turning segmenté.

Le périmètre canonique est admis par le régime opérationnel et satisfait la spécification définie indépendamment.

La continuation stricte :

```text
h⁺ := oneStepAfterPerimeter P
```

est néanmoins générée intérieurement et reste exactement réalisable dans toute `ConcreteContinuationAlgebra P` fournie.

En même temps :

```text
¬ CircularRefinement P h⁺

¬ CircularSpecificationSatisfaction P h⁺
```

La seconde réfutation est démontrée par la spécification indépendante et non simplement déduite du rejet par le régime.

Le candidat canonique possède donc le statut :

```text
engendré intérieurement                  oui
continu constitutivement                 oui
exactement réalisable                    oui
admis par le régime courant              non
satisfait la spécification courante      non
```

C'est le phénomène opérationnel appelé **OOD structurel** dans le projet.

Il s'agit d'une interprétation architecturale du résultat formel, non d'un OOD statistique.

La distinction cruciale est :

```text
changement de statut
≠
perte de détermination
```

---

## 8. Identité

Dans ce projet, **l'identité** est une interprétation architecturale de lois de transport structurel vérifiées.

Elle signifie la persistance d'une détermination constitutive à travers des couches distinctes au moyen de transports exacts.

L'identité n'est pas définie par :

```text
même lecture
même étiquette
même état final
même nombre d'éléments
```

Le projet démontre plutôt les correspondances nécessaires pour suivre l'occurrence elle-même.

Cela permet aux différences de statut et de représentation de rester visibles pendant que la détermination est préservée.

Sous forme condensée :

```text
même détermination
≠ même statut
≠ même réalisation
≠ même lecture
```

L'identité est la persistance de la première à travers des transformations où les autres peuvent varier.

---

## 9. Le résidu opérationnel est l'identité constitutive fraîche

L'alignement constitutif générique à un pas expose une décomposition exacte ancien/nouveau :

```text
Initial ⊕ Unit
    ≃
Extended
```

La composante fraîche n'est pas un second objet introduit à côté du résidu opérationnel.

Dans l'instance circulaire réelle, le dépôt démontre :

```text
fresh de l'alignement à un pas
=
occurrence résiduelle consommée par le turning opérationnel
```

au moyen de :

```lean
StructuralEntrypoint.oneStepAlignmentFreshIsConsumedResidual
```

Cette identification est ancrée définitionnellement : les deux descriptions se réduisent finalement au même terme d'occurrence. La couche d'alignement n'introduit donc pas un objet indépendant qui serait ensuite mis en correspondance avec le résidu.

Le théorème concret correspondant :

```lean
canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
```

transporte cette identité dans toute réalisation canonique induite par une `ConcreteContinuationAlgebra` fournie.

Le mécanisme est donc :

```text
avant la frontière
───────────────────
le nouveau résidu est déterminé

à la frontière
───────────────
ce résidu est l'identité constitutive fraîche

après la frontière
──────────────────
l'identité fraîche devient une identité ancienne
pour toute extension ultérieure
```

Cette transition ancien/fresh constitue le pont entre détermination résiduelle et persistance finie.

---

## 10. Alignement relatif

Aligner ne signifie pas rendre deux réalisations numériquement similaires ou sémantiquement identiques.

Pour ce projet :

> **L'alignement est la persistance cohérente d'une détermination constitutive à travers des réalisations exactes distinctes et des extensions constitutives.**

Cette phrase est une interprétation architecturale des équations vérifiées de transport et de naturalité.

À un pas, les anciennes identités restent anciennes, l'identité fraîche reste distincte d'elles, et les transports entre réalisations exactes préservent les deux branches.

À profondeur finie, le même mécanisme est itéré sur les histoires réellement produites par `generate` et `appendGenerated`.

Chaque étape générée contribue une identité fraîche tout en conservant toutes les identités déjà constituées.

Schématiquement :

```text
profondeur n

old₀
old₁
...
oldₙ₋₁
+
freshₙ
        ↓ extension

profondeur n+1

old₀
old₁
...
oldₙ₋₁
oldₙ        ← fresh précédent
+
freshₙ₊₁
```

Le projet démontre que des identités nées à des profondeurs distinctes restent distinctes après plongement dans un carrier ultérieur commun.

---

## 11. Persistance finie et naturalité

Pour les profondeurs finies, le projet démontre :

- la persistance des identités déjà constituées ;
- exactement une identité fraîche par étape générée ;
- la distinction des identités nées à des profondeurs différentes ;
- la composition des extensions verticales ;
- la composition des transports horizontaux entre réalisations ;
- l'indépendance ponctuelle vis-à-vis du témoin `DepthExtension` fourni ;
- la naturalité entre extension et changement de réalisation.

Le carré central est :

```text
réalisation A à la profondeur s
        ───── extension dans A ─────→
réalisation A à la profondeur t
        │                             │
        │ transport A→B               │ transport A→B
        │                             │
        ↓                             ↓
réalisation B à la profondeur s
        ───── extension dans B ─────→
réalisation B à la profondeur t
```

avec commutation ponctuelle :

```text
T[A,B]^t(E[A]^{s,t}(x))
=
E[B]^{s,t}(T[A,B]^s(x)).
```

Ainsi :

```text
étendre puis changer de réalisation
=
changer de réalisation puis étendre
```

L'extension par des profondeurs intermédiaires et le transport par des réalisations intermédiaires se composent de manière cohérente.

Le dépôt ne possède ni objet d'histoire infinie ni carrier concret à l'étape ω. La persistance est néanmoins uniforme pour toute profondeur finie arbitraire, plutôt qu'énoncée par un théorème distinct pour chaque profondeur.

---

## 12. Persistance du résidu opérationnel

Puisque la première identité fraîche est exactement l'occurrence résiduelle opérationnelle, la machinerie générale de persistance finie s'applique à cet objet produit opérationnellement.

La façade publique expose :

```lean
finiteOperationalResidualPersists
```

et :

```lean
finiteOperationalResidualNaturality
```

La chaîne établie est donc :

```text
résidu opérationnel
        ↓
identité constitutive fraîche
        ↓
persistance finie
        ↓
transport exact entre réalisations
        ↓
naturalité entre réalisations
```

Cela ne transporte **pas** le statut négatif d'admission lui-même à travers toutes les profondeurs ultérieures.

Ce qui persiste est l'identité de l'occurrence qui a marqué la première frontière opérationnelle.

---

## 13. Réalisation exacte et bus structurel

Une réalisation concrète n'est pas acceptée simplement parce qu'elle produit une sortie.

Une `ExactHistoryInterpretation` fournit :

```text
occurrence libre → occurrence concrète

occurrence concrète → occurrence libre

backward(forward(x)) = x

forward(backward(y)) = y
```

ainsi qu'un accord structurel pour l'occurrence réalisée.

Pour le périmètre canonique, le projet dispose de correspondances exactes :

```text
positions périmétrales
        ≃
occurrences libres
        ≃
occurrences concrètes
```

Pour deux réalisations exactes fournies `A` et `B`, leur coordination est induite par cet index structurel commun.

Elle n'est pas introduite comme un matching pair-à-pair indépendant.

Schématiquement :

```text
                  identité structurelle
                  /                  \
                 /                    \
                ↓                      ↓
         réalisation A          réalisation B
```

Le transport induit satisfait :

```text
T[A,B](c_A(p)) = c_B(p)
```

et, en passant par une troisième réalisation :

```text
T[B,C](T[A,B](x)) = T[A,C](x).
```

Cette architecture est appelée **bus structurel**.

Elle fournit une co-indexation exacte.

Elle n'affirme pas un accord sémantique entre des valeurs fournies indépendamment, et l'interface abstraite du bus n'affirme pas elle-même l'unicité parmi tous les bus exacts possibles.

---

## 14. Les lectures viennent après la constitution

Une fois les occurrences et leurs correspondances exactes établies, des lectures arbitraires peuvent être branchées :

```text
Occurrence → Value
```

Le type de valeur est indépendant de la constitution.

Une lecture peut être :

- injective ;
- non injective ;
- constante ;
- numérique ;
- symbolique ;
- à valeurs dans des types.

Aucune de ces possibilités ne modifie l'identité de l'occurrence.

Le transport d'une lecture est un reindexage le long d'un transport structurel déjà établi.

La direction est :

```text
constitution des occurrences
→ correspondances exactes
→ famille ouverte de lectures
```

et non :

```text
lectures concordantes
→ identité reconstruite
```

Une égalité de valeurs de lecture n'est jamais utilisée comme substitut à l'égalité des occurrences constituées.

---

## 15. Norme relative et régime opérationnel

Le projet distingue quatre niveaux :

```text
Construction(H)

F_A(H) := ExactConcreteRealization A H

R(H)   := CircularRefinement P H

S(H)   := CircularSpecificationSatisfaction P H
```

Ils répondent à des questions différentes :

| Couche | Question |
|---|---|
| constitution | l'objet peut-il être formé ? |
| réalisation fidèle | l'objet est-il exactement préservé dans cette implémentation ? |
| régime | l'objet est-il admis opérationnellement ? |
| norme | l'objet satisfait-il la spécification indépendante ? |

La norme n'est pas définie comme « ce que le régime accepte ».

Le projet construit au contraire :

```text
R(H) → S(H)

S(H) → H = perimeterDeployment P

S(H) → R(H)
```

au moyen de :

```lean
circularRefinement_soundSpecification

CircularSpecificationSatisfaction.eq_perimeter

circularSpecification_complete
```

Régime et norme classifient donc les mêmes histoires dans l'instance circulaire tout en conservant des types de témoins, des définitions et des chemins de preuve distincts.

Le but n'est pas de les fusionner en une seule notion.

Le but est de faire de leur adéquation un théorème.

---

## 16. Diagnostic structurel

Une sortie de régime n'est pas représentée seulement par :

```text
¬ Regime(candidate)
```

Elle conserve le candidat et les preuves positives de ce qui reste valide.

Le diagnostic canonique conserve, sur la même histoire construite :

```text
candidat

réalisation exacte

rejet par le régime

rejet par la spécification indépendante

information d'adéquation
```

La méthode peut alors énoncer précisément :

> cet objet existe toujours,
> cette structure reste préservée,
> cette implémentation le réalise toujours exactement,
> et voici la propriété opérationnelle ou normative exacte qui ne tient plus.

C'est la notion de diagnostic relatif du projet.

---

## 17. Cohérence médiée

Le dépôt isole également un mécanisme générique de commutation médiée.

Son résultat fondamental est la **commutation observée sans aucune hypothèse de fidélité** :

```lean
MediatedTransitionCoherence.observed_commutation
```

L'égalité littérale peut ensuite être récupérée lorsque les valeurs observées pertinentes sont réfléchies :

```lean
MediatedTransitionCoherence.commute_of_local_reflection
```

L'injectivité globale est une manière suffisante de fournir cette réflexion :

```lean
MediatedTransitionCoherence.commute
```

La distinction est importante :

```text
commutation observée
ne requiert pas de fidélité

commutation littérale
requiert la réflexion de l'égalité pertinente
```

Le dépôt n'affirme pas que l'hypothèse de réflexion locale soit, en présence de toutes les autres hypothèses, automatiquement une condition logiquement strictement plus faible que la conclusion littérale elle-même.

Au niveau de l'alignement fini, des carrés adjacents de naturalité peuvent aussi être collés.

La suite de régression contient un modèle avec une observation intermédiaire prouvée non injective dans lequel la commutation observée extérieure est conservée ; la réflexion terminale permet alors de récupérer le carré littéral extérieur.

---

## 18. Frontière représentationnelle

`RepresentationBoundary` est une branche séparée.

Elle ne produit pas la continuation opérationnelle et n'établit pas la persistance constitutive.

Son noyau autonome reçoit un évaluateur :

```text
eval : Code → Code → Prop
```

et définit :

```lean
diagonalStatus eval code := ¬ eval code code
```

Il démontre ensuite constructivement que ce prédicat diagonal n'est pas représentable intérieurement :

```lean
diagonalStatus_notRepresentable
```

et donc que la clôture représentationnelle globale échoue :

```lean
noGlobalRepresentationClosure
```

Il s'agit d'un résultat sémantique de non-représentabilité diagonale.

Ce n'est pas une formalisation de l'incomplétude de Gödel, de la syntaxe, de la prouvabilité ou de l'arithmétisation.

---

## 19. Représentation des statuts circulaires

Le régime opérationnel circulaire et la spécification indépendante possèdent des statuts propositionnels :

```text
CircularRegimeStatus P H

CircularSpecificationStatus P H
```

obtenus en observant leurs types de témoins au moyen de `Nonempty`.

Les applications de témoins déjà établies fournissent leur adéquation propositionnelle.

Une représentation exacte fournie de l'un de ces statuts déterminés peut donc être transportée vers l'autre.

L'application de frontière représentationnelle combine :

```text
représentation exacte de statuts déterminés choisis

+

non-représentabilité du statut diagonal de l'évaluateur
```

sans identifier le candidat opérationnel au prédicat diagonal.

Les deux sorties restent distinctes :

```text
sortie opérationnelle
=
une histoire constituée dont le statut d'admission change

sortie représentationnelle
=
un prédicat non représentable intérieurement par un évaluateur
```

Aucun théorème ne convertit un objet dans l'autre.

---

## 20. Résultats sélectionnés vérifiés par la machine

| Résultat | Ancrage Lean principal |
|---|---|
| la réalisation locale exacte reconstruit le périmètre | `ExactNonClosingRealization.toPerimeterExtension` |
| la continuation stricte après le périmètre existe | `oneStepAfterPerimeter`, `oneStepAfterPerimeterStrict` |
| le noyau résiduel positif générique produit une occurrence résiduelle unique | `SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence` |
| occurrence résiduelle réelle à un pas | `StrongPerimetralTurning.oneStepCoreResidualOccurrence` |
| la continuation reste exactement réalisable | `exactlyInterpretHistory` |
| la continuation quitte le régime opérationnel | `oneStepAfterPerimeter_notCircularRefinement` |
| la continuation échoue à la spécification indépendante | `oneStepAfterPerimeter_notSpecificationSatisfaction` |
| le fresh du premier alignement est le résidu opérationnel consommé | `oneStepAlignmentFreshIsConsumedResidual` |
| persistance finie du résidu opérationnel | `finiteOperationalResidualPersists` |
| naturalité de la persistance du résidu | `finiteOperationalResidualNaturality` |
| les extensions se composent | `Alignment.FiniteConstitutiveAlignment.Realization.extend_comp` |
| les transports entre réalisations se composent | `Alignment.FiniteConstitutiveAlignment.Realization.transport_comp` |
| extension et changement de réalisation commutent | `Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_natural` |
| les identités nées à des profondeurs distinctes restent distinctes | `Alignment.IteratedCarrier.fresh_ne_fresh_of_depth_ne` |
| les distinctions déjà présentes dans une lecture persistent | `Alignment.ReadoutPersistence` |
| les carrés médiés commutent au niveau observé sans fidélité | `MediatedTransitionCoherence.observed_commutation` |
| l'égalité littérale suit lorsque les valeurs pertinentes sont réfléchies | `MediatedTransitionCoherence.commute_of_local_reflection`, `commute` |
| les carrés médiés adjacents se collent | `Alignment.MediatedTransitionPasting` |
| le statut diagonal n'est pas représentable intérieurement | `diagonalStatus_notRepresentable` |
| la clôture représentationnelle globale échoue | `noGlobalRepresentationClosure` |

---

## 21. Ce que le projet ne revendique pas

Le développement actuel n'établit pas :

- un accord sémantique entre des lectures fournies indépendamment ;
- l'unicité inconditionnelle de toute correspondance exacte ;
- une théorie universelle de tout problème d'alignement possible ;
- l'alignement comportemental de systèmes d'IA arbitraires ;
- des garanties sur des modèles d'apprentissage entraînés à grande échelle ;
- un objet d'histoire infinie ou un carrier concret à l'étape ω ;
- l'égalité entre sortie opérationnelle et sortie représentationnelle ;
- un théorème d'incomplétude de Gödel ;
- une non-représentabilité universelle indépendante de l'évaluateur fourni ;
- que la méthode des rôles constitutifs relationnels soit déjà un métathéorème Lean universel.

La persistance finie est néanmoins quantifiée uniformément sur toute profondeur cible finie arbitraire.

---

## 22. Architecture des sources

### Fondations structurelles et résiduelles

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean)  
  isole les dépendances nécessaires à la détermination résiduelle, les conditions de reconstruction et la compatibilité avec l'interface historique plus riche.

- [`SegmentedResidualRoleStrictness.lean`](SegmentedResidualRoleStrictness.lean)  
  fournit des séparateurs positifs montrant où le noyau résiduel plus faible diverge du contrat plus riche de réalisation interne.

- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean)  
  définit les structures génériques de frontière, classification de régime, turning et obstruction indépendamment de la circularité.

- [`ExactTypeTransport.lean`](ExactTypeTransport.lean)  
  fournit des transports exacts constructifs à deux sens et leurs lois de composition.

### Producteur circulaire

- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean)  
  implémente la présentation circulaire, le générateur constitutif, les histoires, la reconstruction local/global, la réalisation concrète, le régime opérationnel, la norme indépendante et l'instance circulaire du turning.

### Alignement et persistance

- [`Alignment/Constitutive.lean`](Alignment/Constitutive.lean)  
  définit l'alignement constitutif générique exact à un pas, ancien/fresh.

- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean)  
  dérive la persistance finie, la structure des identités entre profondeurs, le transport entre réalisations, la composition et la naturalité.

- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)  
  ajoute les lectures en aval de l'identité et démontre la persistance des distinctions déjà établies.

- [`MediatedTransitionCoherence.lean`](MediatedTransitionCoherence.lean)  
  fournit le noyau générique de commutation observée et de réflexion.

- [`Alignment/MediatedTransitionCoherence.lean`](Alignment/MediatedTransitionCoherence.lean)  
  instancie la cohérence médiée pour l'alignement constitutif fini.

- [`Alignment/MediatedTransitionPasting.lean`](Alignment/MediatedTransitionPasting.lean)  
  démontre la composition et le collage de carrés adjacents de naturalité médiée.

### Instance circulaire de persistance

- [`StrongPerimetralTurning/ConstitutivePersistence.lean`](StrongPerimetralTurning/ConstitutivePersistence.lean)  
  raccorde la continuation circulaire à un pas à l'alignement constitutif générique et identifie l'identité fraîche à l'occurrence résiduelle opérationnelle.

- [`StrongPerimetralTurning/IteratedConstitutivePersistence.lean`](StrongPerimetralTurning/IteratedConstitutivePersistence.lean)  
  instancie la persistance finie sur les histoires réellement générées par le producteur circulaire.

### Façade structurelle publique

- [`StructuralEntrypoint.lean`](StructuralEntrypoint.lean)  
  présente à échelle humaine les principaux raccords structurels vérifiés sans devenir une dépendance de leurs preuves.

### Frontière représentationnelle

- [`RepresentationBoundary/DiagonalizationKernel.lean`](RepresentationBoundary/DiagonalizationKernel.lean)  
  contient le noyau diagonal constructif autonome.

- [`RepresentationBoundary/CircularStatusRepresentation.lean`](RepresentationBoundary/CircularStatusRepresentation.lean)  
  applique ce noyau aux statuts propositionnels circulaires.

- [`RepresentationBoundary.lean`](RepresentationBoundary.lean)  
  est l'agrégateur public, sans preuve propre, de la branche de frontière représentationnelle.

### Validation et exemples exécutables

- [`Tests/ResidualAuditRegression.lean`](Tests/ResidualAuditRegression.lean)  
  teste la factorisation du noyau résiduel et le comportement des séparateurs.

- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean)  
  exerce la persistance finie et la séparation des identités.

- [`Tests/MediatedTransitionCoherenceRegression.lean`](Tests/MediatedTransitionCoherenceRegression.lean)  
  teste la commutation médiée et les hypothèses porteuses du noyau générique.

- [`Tests/MediatedTransitionPastingRegression.lean`](Tests/MediatedTransitionPastingRegression.lean)  
  contient notamment la régression de collage avec intermédiaire non fidèle.

- [`Examples/ConcreteContinuation/LoggedAlgebra.lean`](Examples/ConcreteContinuation/LoggedAlgebra.lean)  
  fournit une réalisation concrète constructive non identitaire.

- [`Examples/Alignment/IteratedReadout.lean`](Examples/Alignment/IteratedReadout.lean)  
  calcule des lectures non constantes à travers plusieurs étapes générées et des réalisations distinctes.

---

## 23. Documentation

Présentation théorique principale :

- [Présentation longue — français](PRESENTATION_LONGUE.md)

Pour les arguments complets et les détails méthodologiques :

- [Fondements structurels](docs/fr/fondements_structurels.md)
- [Instance circulaire — alignement relatif](docs/fr/alignement_relatif.md)
- [Méthode des rôles constitutifs relationnels](docs/fr/methode_roles_constitutifs_relationnels.md)
- [Frontière représentationnelle](docs/fr/frontiere_representationnelle.md)
- [Carte architecturale vérifiée](docs/fr/cartographie_architecturale_verifiee.md)
- [Compilation et audit axiomatique](audit/AUDIT_BUILD.txt)
- [Déclaration de conception](AI_AUTHORSHIP.md)

Les équivalents anglais sont fournis pour la documentation scientifique.

---

## 24. Reproduction

Le dépôt est un artefact autonome : aucun historique source privé n'est nécessaire pour le compiler ou l'inspecter.

Avec `elan`, ou un environnement équivalent lisant `lean-toolchain` :

```bash
lake clean
lake build
lake build AuditRegression
```

Vérifier le manifeste des sources scientifiques sous Linux ou macOS :

```bash
bash scripts/verify-manifest.sh
```

Sous PowerShell 7 :

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

ou sous Windows PowerShell :

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

`MANIFEST.sha256` couvre les sources Lean publiées et les documents scientifiques canoniques qui y sont listés.

Les métadonnées du dépôt et les documents d'accès sont hors de ce manifeste de sources scientifiques. En particulier, le manifeste n'ancre pas par hachage :

```text
README.md
README_fr.md
lean-toolchain
lakefile.toml
lake-manifest.json
.github/workflows/lean.yml
audit/AUDIT_BUILD.txt
MANIFEST.sha256
```

Leur identité est donc fixée par le commit Git audité plutôt que par `MANIFEST.sha256`.

La CI du projet exerce le développement sous Linux et Windows.

---

## 25. Constructivité et discipline d'audit

Le développement scientifique est conçu pour rester constructif.

Le dépôt scanne et audite les déclarations sources pertinentes vis-à-vis de dépendances ou constructions telles que :

```text
axiom
sorry
admit
Classical
noncomputable
propext
Quot.sound
```

Chaque source Lean se termine par un bloc explicite `#print axioms`.

Ces blocs nomment un ensemble sélectionné de déclarations dans chaque fichier : la couverture est complète dans certains petits modules et volontairement partielle dans des modules plus importants comme `StrongPerimetralTurning.lean`.

Chaque déclaration nommée dans ces blocs d'audit est rapportée par Lean comme ne dépendant d'aucun axiome.

Sur l'arbre actuellement audité, la compilation complète émet 1 161 lignes de la forme :

```text
does not depend on any axioms
```

et zéro ligne de la forme :

```text
depends on axioms
```

Les modèles séparateurs et les tests de régression servent non seulement à démontrer les cas positifs, mais aussi à tester les frontières de dépendance et à empêcher que des affirmations plus fortes ne s'introduisent silencieusement via des définitions surcontraintes.

---

## 26. Portée

L'instance complète actuellement vérifiée est circulaire/périmétrale.

La méthode des rôles constitutifs relationnels est plus large comme extraction méthodologique, mais elle n'est pas encore un métathéorème Lean universel.

Un prochain test scientifique majeur serait une seconde instance indépendante et non circulaire utilisant la même discipline :

```text
individuer
→ relier
→ séparer
→ reconstruire
→ transporter
→ diagnostiquer
```

sans redessiner la méthode autour de cette seconde instance.

Une telle instanciation aiderait à distinguer ce qui appartient réellement à la méthode générale de ce qui dépend de la géométrie circulaire.

---

## 27. Vue condensée

Le projet peut être résumé par deux mouvements.

### Mouvement constitutif

```text
détermination structurelle locale
        ↓
reconstruction exacte
        ↓
continuation générée intérieurement
        ↓
occurrence résiduelle
        ↓
changement de statut opérationnel/normatif
        │
        │ sans perte de constitution
        ↓
identité constitutive fraîche
        ↓
persistance finie
        ↓
transport cohérent entre réalisations
        ↓
lecture seulement ensuite
```

### Mouvement représentationnel

```text
statuts propositionnels déterminés
        ↓
représentation exacte
        ↓
transport de représentation

et indépendamment

évaluateur
        ↓
statut diagonal
        ↓
non-représentabilité
        ↓
échec de la clôture représentationnelle globale
```

Les deux mouvements sont structurellement reliés mais formellement distincts.

Le premier étudie la persistance d'une détermination à travers construction, extension, réalisation et changement de statut.

Le second étudie la frontière de la représentation exacte relativement à un évaluateur.

---

## 28. Principe directeur

Le principe directeur du projet est :

> **Préserver l'individuation la plus fine disponible et les relations qui la constituent ; éprouver chaque dépendance sur le carrier le plus faible où elle peut être séparée ; ne reconstruire que ce qui découle de la structure réintroduite ; ne transporter que les déterminations dont la conservation a été démontrée ; puis diagnostiquer une frontière en maintenant, sur le même objet, les témoins positifs de ce qui subsiste et la preuve négative de ce qui cesse d'être satisfait.**

Dans l'instance circulaire, cette discipline soutient l'interprétation architecturale suivante :

> **Les différences de statut sont préservées tandis que des transports exacts permettent à une même détermination constitutive de traverser de manière cohérente des couches et des réalisations distinctes.**

Dans ce sens architectural :

```text
identité
=
persistance d'une détermination constitutive
à travers des transports exacts

alignement
=
persistance cohérente de cette identité
à travers des réalisations et extensions distinctes
```

Ces formulations sont des interprétations contraintes par les théorèmes vérifiés de transport, de persistance et de naturalité.

Elles n'identifient pas les couches traversées.

C'est précisément leur séparation qui donne un sens à la persistance.