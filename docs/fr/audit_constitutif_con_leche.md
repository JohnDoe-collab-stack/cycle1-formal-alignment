# Audit constitutif d’une chaîne de vérification avec ConLeche

[English](../en/constitutive_con_leche_audit.md) | **Français**

## 1. Résultat

Ce développement sépare deux garanties complémentaires :

1. ConLeche contrôle l’objet effectivement présenté à son fold vérifié ;
2. l’analyse constitutive explicite comment cet objet a été formé depuis une
   occurrence source.

La distinction centrale est :

```text
acceptation de l’objet présenté
≠
fidélité de sa formation depuis le source
```

Le module
[`ConstitutiveAlignment/VerificationTransport.lean`](../../ConstitutiveAlignment/VerificationTransport.lean)
formalise cette distinction constructivement. Il ne dépend ni de ConLeche ni de
son modèle en théorie des ensembles.

## 2. Portée du théorème externe

Le théorème principal de ConLeche est relatif à un modèle de son interface
`SetTheory`. Lorsque `checkDecls` en mode `verified` accepte une liste de
déclarations et produit un environnement, cet environnement ne contient aucune
constante dont le type est `False`.

Le résultat porte sur la liste reçue par le fold. Le frontend se situe avant
cette frontière : il parse le flux NDJSON, ajoute un prélude, traite certains
dépendances et blocs inductifs et peut réécrire des fonctions de projection.
Les déclarations ainsi produites sont contrôlées, mais l’équivalence sémantique
complète entre le flux initial et toutes ces transformations n’est pas le
théorème principal.

Le test constitutif nomme exactement l’alignement interne ainsi obtenu :

```text
R(ds, env) = checkDecls .verified ds = .ok env
S(ds, env) = env ne contient aucune constante de type False
```

`no_proof_of_False` établit `R → S`. Dans le code inspecté, la chaîne est
`acceptation → FullyChecked → Nonempty EnvModelM → exclusion de False`. Le
module local reproduit cette forme avec `SemanticChecker.Soundness`, expose sa
factorisation `R → Certificate → S`, puis vérifie par séparateurs que cette
soundness ne produit ni completeness `S → R`, ni fidélité de provenance.

Une recompilation séparée contre le commit épinglé établit en outre que la
dernière flèche se factorise par la projection
`EnvModelM → {base2, type_reads, mem_type}`. Les onze autres champs supérieurs
de `EnvModelM` ne sont donc pas lus directement par le capstone `no False` ; ils
peuvent cependant rester nécessaires à la construction amont de cette
projection. Dans `base2`, cette flèche lit la valuation `acval` et le pin
`basis_pinnedL`. Son extrémité ensembliste consomme seulement un objet vide et
l’impossibilité d’en être membre. `ConstructiveEmptyFoundation.derivedEmpty`
reconstruit positivement ce témoin depuis régularité et un univers transitif
habité, sans choix classique. La chaîne entière `checkDecls → FullyChecked →
slice → no False` recompile contre ConLeche ; à ce stade, sa construction amont
passe encore par le `EnvModelM` complet.

Le test de construction directe a ensuite suivi l'induction réellement utilisée
par `installRun_model`. Son premier pas sémantique appelle
`declStep_preserves` pour chacune des six formes de déclaration. Cette opération
ne prend pas la slice terminale comme invariant : elle consomme et reconstruit le
carrier complet, notamment parce que la vérification d'une nouvelle valeur peut
mobiliser les clauses `const`, définition, iota, projection, littéraux,
capacités et réduction rassemblées par `TierInputsAt.ofSem`. La construction
directe `FullyChecked → slice`, sans passage par le modèle complet, n'est donc
pas obtenue par les lemmes actuels. Le résultat établi est plus précis : la
slice est suffisante pour l'inférence terminale, mais sa clôture inductive sous
toutes les déclarations acceptées reste une obligation distincte.

Le noyau local distingue maintenant la réalisation constructive de son ombre
propositionnelle. `WitnessCandidate` porte un témoin initial et extrait la
garantie terminale ; `ShadowCarrier` n'en conserve que l'existence par
`Nonempty`. `WeaklyStable` demande seulement l'existence d'un successeur, alors
que `HistoricalStable` construit un successeur déterminé relié à l'ancien
témoin par une compatibilité. Les théorèmes `shadowExtract` et
`historicalStable_implies_weaklyStable` établissent les deux oublis valides.
Enfin, un `Separator` réfute soit une reconstruction transitionnelle locale,
soit toute stabilité historique dont la compatibilité fournirait l'obligation
séparée. Le noyau n'affirme ni converse, ni fermeture canonique, ni minimalité.

Le weakening du séparateur concret affine maintenant cette frontière. Une
enveloppe locale suffisante factorise les trois branches à valeur `defn`, `thm`
et `opaque` par trois faits : bonne dénotation de la valeur, appartenance au
type inféré et accord sémantique entre type inféré et type déclaré. Dans le
premier contre-modèle, les deux premiers faits sont construits positivement et
le troisième est réfuté. L'obligation `Q0`, indexée par la transition réelle et
le témoin antérieur, est donc réduite à ce seul accord historique pour cette
transition. Elle est portée dans `Type` par `PLift`, car les certificats
d'exécution de ConLeche vivent dans `Prop`. Pour la transition concrète,
`B0W + Step + Q0` produit bien les deux `CheckedValueLocalRows`, tandis que le
séparateur réfute exactement `Q0`.

Le test générique strict s'est ensuite arrêté sur la première branche demandée,
`defn`. Un second témoin concret de `B0W` attribue à un alias stocké une
interprétation dans `U₀`, alors que le checker déplie opérationnellement ce même
alias comme un type de fonctions. Une fonction stockée est terminalement bien
typée dans la slice affaiblie, et une nouvelle définition qui l'applique est
accompagnée d'un véritable `DeclDefnRun` construit positivement. Pourtant,
l'application ne peut pas être `WellDenoted` : au niveau zéro, sa prétendue
fonction devrait être `pt` ; à un niveau positif, son graphe devrait être égal
à `unitSet`. Les deux cas sont réfutés constructivement. Le théorème
`b0WDefnStepDoesNotProduceValueWellDenoted` établit donc la séparation concrète

```text
B0W + DefnStep accepté
  ↛ valueWellDenoted.
```

L'analyse locale descend ensuite d'un étage sans ouvrir `WellDenoted`. Le
théorème `ValueFrontRun.appSubtermReads` montre que, lorsque la sortie annotée
d'un véritable `ValueFrontRun` est une application, la tête et l'argument ont,
pour chaque valuation de niveaux `ψ`, des lectures `denoteMeta` réussies. La
preuve consomme seulement `slice.base2`, le `ValueFrontRun` et l'égalité qui
identifie sa sortie à une application. Elle ne consomme ni `ConstantValRun`, ni
`type_reads`, ni `mem_type`, ni le témoin eta. Ce résultat n'est toutefois pas
purement syntaxique : `acceptedReads_of` utilise le modèle `base2` et le succès
d'inférence déjà contenu dans `ValueFrontRun`. La couche de lecture ne produit
donc aucun nouveau séparateur.

Le test s'arrête en revanche immédiatement sur la première ligne sémantique.
`ApplicationHeadWellDenoted` conserve l'ordre acquis des quantificateurs : pour
chaque `ψ`, les mêmes lectures `headA` et `argA` doivent servir pour tout `ρ`.
Le théorème `appReadsDoNotDetermineHeadWellDenoted` construit un témoin `B0W`,
un véritable `ValueFrontRun` dont la sortie est applicative et les deux lectures
pour chaque `ψ`, puis réfute toute attribution de `WellDenoted` à cette même
tête pour tous les `ρ`. Le contre-modèle place l'application sémantiquement
incohérente déjà établie dans le corps d'une lambda opérationnellement acceptée,
puis utilise cette lambda comme tête d'une application extérieure. La lecture
de la tête est donc déterminée, mais sa bonne dénotation ne suit pas :

```text
B0W + ValueFrontRun + lectures head/argument
  ↛ ∀ ρ, WellDenoted ρ headA.
```

L'ouverture exacte de `WellDenoted_lam` localise encore cette rupture. Sa
première clause, la bonne dénotation du domaine `Sort 0`, est construite sans
le témoin de parcours ni mémoire sémantique supplémentaire. La deuxième
clause exige que le corps reste bien dénoté sous toute extension de `ρ` par un
élément du domaine. `outerHeadBodyHereditaryFails` la réfute déjà en choisissant
le vide, qui appartient à l'interprétation de `Sort 0`, puis en réutilisant le
séparateur de l'application interne. La troisième clause, qui quantifie une
fibre sémantique, n'est pas ouverte. Le premier résidu interne est donc la
bonne dénotation héréditaire du corps, non la bonne dénotation du domaine.

L'ouverture de cette clause héréditaire s'arrête à son tour au premier résidu
de l'application interne. `argReadExact` fixe sa lecture comme le produit
annoté attendu. `innerApplicationHeadWellDenoted` et
`innerApplicationArgumentWellDenoted` ferment alors les deux clauses
récursives de `WellDenoted_app` : la tête constante et l'argument sont tous
deux bien dénotés. `InnerApplicationFrame` conserve ensuite le même `v`, le
même domaine `A` et la même fibre `B` pour les trois clauses sémantiques
restantes. Le weakening interne montre toutefois que la première clause suffit
déjà à la contradiction : `innerApplicationHeadInPiRFails` réfute, pour tout
`v`, `A` et `B`, l'appartenance de la lecture `unitSet` de `punit` à
`piR v A B`. Au niveau zéro, elle imposerait `unitSet = pt`; à niveau positif,
elle imposerait que `unitSet` soit un graphe, alors que son élément `pt` n'est
pas une paire. `argumentInA` et `zeroCondition` ne sont donc pas consommées par
ce séparateur. Leur reconstructibilité n'est pas analysée.

La preuve positive réelle de la clause `headInPiR` est ensuite factorisée sans
désolidariser ses objets intermédiaires. Le lemme
`headInPiR_of_membership_and_reduction` consomme une appartenance `M` de la
lecture de la tête à la lecture d'un type inféré, une égalité de réduction `R`
entre ce même type inféré et le `forall` réduit, puis la lecture exacte de ce
`forall` comme le `piR` correspondant. Dans le contre-modèle,
`innerHeadMembershipInInferredType` construit positivement `M` : `punit` est
lu comme `unitSet`, qui appartient à `univ 0`, lecture du type inféré `Sort 0`.
`aliasWhnfAndRead` conserve ensemble le `WhnfRun` concret et la lecture du
corps qu'il produit : le `forall` réduit n'est pas choisi indépendamment. En
revanche,
`inferredTypeReductionAgreementFails` réfute `R` : identifier `univ 0` à cette
lecture fonctionnelle produirait précisément l'appartenance `headInPiR` déjà
réfutée. Ainsi, dans ce contre-modèle, la première dépendance résistante de
cette factorisation est `R`, non `M`.

Ce résultat ne fait de `R` ni une condition minimale, ni une nécessité
universelle, ni encore une mémoire historique identifiée. Il localise seulement
la rupture de cette preuve positive concrète tout en conservant le même type
inféré et le même `forall` réduit dans les deux prémisses.

L'ouverture de la preuve positive de `R` descend ensuite dans la branche δ de
`whnfLoop_claim`. Cette branche utilise `Delta`, que l'architecture générale
construit depuis `AcvalDefnInst`. Le weakening n'importe toutefois ni
`WhnfClaim` ni `AcvalDefnInst` comme nouvelle primitive. Il isole leur
conséquence locale exacte, `AliasDeltaReadingCoherence` : pour cette réduction,
la lecture de la constante avant dépliage doit être identique à la lecture du
corps effectivement déplié.

`aliasDeltaReading_of_Delta` montre que `Delta` produit cette relation locale,
et `aliasDeltaReading_of_acvalDefnInst` enregistre la chaîne suffisante depuis
le champ général. Réciproquement au niveau requis ici,
`inferredTypeReductionAgreement_of_aliasDeltaReading` montre que cette seule
égalité de lectures suffit à reconstruire `R`; elle conserve les annotations
fixées par `aliasInferredTypeRead`, `aliasWhnfAndRead` et `aliasBodyRead`.

Le séparateur atteint alors cette relation elle-même.
`aliasDeltaReadingCoherenceFails` la réfute, et
`b0WAndWhnfDoNotDetermineAliasDeltaReading` empaquette un témoin `B0W`, le
`whnf` concret et cette réfutation. Enfin, `oldSlice_hasNoAcvalDefnInst` montre
que le contre-modèle ne peut pas satisfaire le champ général, précisément parce
que son instance sur l'alias imposerait la relation locale réfutée. Le résultat
n'établit toujours ni que `AcvalDefnInst` entier est nécessaire, ni que cette
relation locale est minimale dans une classe générale, ni qu'elle doit être
persistée dans un futur `B1`.

Un weakening supplémentaire montre que même l'égalité sémantique complète `R`
n'est pas consommée par la dernière étape. `AliasDeltaHeadMembershipTransport`
est indexé par la réalisation `old.slice`, par `ψ` et par `ρ`; il transporte
seulement l'appartenance déjà disponible de la lecture de cette tête précise,
depuis la lecture de son type avant δ vers la lecture du type réduit.
`aliasDeltaHeadMembershipTransport_of_reductionAgreement` établit `R →`
transport, et la cohérence de lectures produit donc également ce transport.
Puis `innerHeadInPiR_of_aliasDeltaHeadMembershipTransport` combine uniquement
ce transport avec `M` pour obtenir la clause `headInPiR` exacte.

Le weakening ne répare pas le contre-modèle :
`aliasDeltaHeadMembershipTransportFails` réfute déjà le transport orienté, et
`b0WAndWhnfDoNotDetermineHeadMembershipTransport` conserve dans le même énoncé
le témoin `old.slice`, le `whnf` concret et cette réfutation pour tous `ψ` et
`ρ`. Mais `aliasDeltaHeadMembershipTransport_iff_innerHeadInPiR` établit une
limite décisive du weakening : pour cette occurrence entièrement fixée, `M`
est déjà disponible et la cible du transport est exactement `headInPiR`; le
transport est donc équivalent à la conclusion elle-même. Il ne constitue pas
encore une capacité intermédiaire stricte. L'égalité `R` reste une enveloppe
suffisante, mais aucun non-converse entre transport et égalité n'est démontré.
Affaiblir davantage ce transport local reviendrait ici à réénoncer la cible.

Le weakening change alors de niveau. `UniformMembershipPreservation` quantifie
sur toute valuation ensembliste `ρ` et sur tout objet `x` : toute appartenance
à la lecture avant transformation doit être transportée vers la lecture après
transformation. Cette relation couvre donc uniformément une famille entière de
jugements d'appartenance, au lieu de renommer la conclusion d'une occurrence
unique.

`uniformMembershipPreservation_of_semanticEquality` montre que l'égalité
sémantique uniforme implique cette relation. Pour l'alias courant,
`aliasDeltaReading_implies_uniformMembershipPreservation` effectue ce passage,
puis `innerHeadInPiR_of_uniformMembershipPreservation` récupère la conclusion
particulière à partir de `M`.

Cette fois, la faiblesse est stricte et non vacueuse. Un second dépliage δ
concret porte sur `GrowingType`, dont le corps stocké est `Sort 1`, alors que
la réalisation affaiblie lit la constante comme `Sort 0`.
`growingTypeDeltaUnfold` et `growingTypeDeltaReads` fixent le même dépliage et
ses deux lectures exactes. `growingTypeDelta_uniformMembershipPreservation`
établit le transport de toute appartenance par cumulativité de `univ 0` vers
`univ 1`, et `growingTypeDelta_hasPreservedMembership` exhibe `empty` comme
appartenance effectivement conservée. Pourtant,
`growingTypeDelta_semanticEqualityFails` réfute l'égalité : elle transformerait
`univ 0 ∈ univ 1` en l'auto-appartenance impossible `univ 0 ∈ univ 0`. Ainsi,
dans la classe des jugements d'appartenance étudiée :

```text
égalité sémantique uniforme
        ↓
préservation uniforme des appartenances
        ↓
appartenance particulière requise

mais

préservation uniforme des appartenances
        ↛ égalité sémantique uniforme
```

Le raccord au contre-modèle initial est ensuite direct mais conserve toutes
les indexations. `aliasUniformMembershipPreservationFails` applique la
relation uniforme au même `ψ`, au même `ρ` et à l'appartenance `M`, puis atteint
le même `headInPiR` réfuté. Le théorème
`b0WAndWhnfDoNotDetermineUniformMembershipPreservation` rassemble un unique
témoin `B0W`, le `whnf` concret du même alias, la lecture exacte de son résultat
pour chaque `ψ` et la réfutation de la préservation uniforme entre la lecture
ancienne et cette lecture réduite. Il établit donc :

```text
B0W + dépliage concret de l'alias
        ↛ préservation uniforme des appartenances
```

L'audit transversal affine encore cette capacité. Les consommateurs réels ne
demandent le transport que pour les valuations `ρ` satisfaisant le contexte
annoté `Δa`. `GuardedMembershipPreservation` exprime exactement cette garde,
et `WhnfMembershipClaim` conserve la bonne dénotation du réduit tout en
remplaçant l'égalité de `WhnfClaim` par ce seul transport. Trois reconstructions
compilent avec cette interface affaiblie : la voie canonique `SortSemAt`, la
voie IO `SortSemAtIO` et la ligne structurelle `StructEtaIrrel`. Il ne s'agit
donc plus d'une capacité ajustée à une occurrence unique ni d'un simple miroir
entre deux voies du checker.

Le même contre-modèle la réfute déjà dans le contexte vide :
`b0WAndWhnfDoNotDetermineGuardedMembershipPreservation` conserve un même témoin
`B0W`, le même dépliage concret et sa lecture exacte, puis montre que même cette
relation gardée n'est pas reconstructible. L'égalité reste suffisante pour la
produire. Le même témoin `GrowingType` fournit désormais le non-converse direct
et non vacue `GuardedMembershipPreservation ↛ égalité` dans le contexte vide,
sans effacer la séparation déjà acquise pour `UniformMembershipPreservation`.

L'analyse inversée du producteur δ donne une première chaîne exacte, sans en
faire encore une interface commune aux autres réductions : `AcvalDefnInst`
construit `Delta`; `Delta` force l'identité de l'annotation lue avant et après
le dépliage concret; cette identité produit la préservation gardée. Cela
identifie la donnée amont réellement utilisée par le producteur δ, mais ne
démontre ni qu'elle est minimale, ni qu'elle doit persister dans `B1`.

`unfoldDefinition_exposesExactSpine` fixe maintenant la classe opérationnelle
transportée par `delta_core`. Un dépliage réussi expose une tête constante, la
`defnInfo` stockée correspondante, l'accord d'arité des niveaux, puis une cible
exactement égale au corps instancié auquel `source.getAppArgs` est réappliqué.
La spine est donc une liste finie syntaxique arbitraire, conservée dans le même
ordre. `denoteMeta_mkAppN_swap` ne demande à ce niveau ni typage, ni `Sat`, ni
`WellDenoted`; le succès de lecture du terme complet force les lectures
nécessaires des arguments. `ψ` et la profondeur sont fixes, tandis que `ρ`
n'apparaît pas encore.

Cette classe exacte de contextes engendre maintenant une relation intermédiaire
formelle. `ReadableApplicativeMembershipSimulation` est indexée par `acval`,
l'environnement, `ψ` et la profondeur. Elle n'admet une spine annotée que si
`DenoteMetaSpine` prouve qu'elle est la lecture effective d'une même spine
syntaxique. Toute appartenance observée après cette spine sur `before` doit
rester valide après la même spine, dans le même ordre, sur `after`, uniformément
en `ρ`. L'ajout d'un argument exige explicitement son équation de lecture.
La relation n'incorpore ni `Sat`, ni typage, ni `WellDenoted`.

`ApplicativeMembershipSimulation` est l'enveloppe plus forte qui quantifie sur
toutes les listes d'`AnnotTerm`; elle se restreint à l'interface exacte pour
n'importe quel contexte de lecture. Les preuves établissent donc :

```text
égalité sémantique uniforme des têtes
        ↓
ApplicativeMembershipSimulation
        ↓ restriction aux lectures effectives
ReadableApplicativeMembershipSimulation
        │ stable sous un argument effectivement lu
        │ stable sous tout DenoteMetaSpine commun
        ↓
GuardedMembershipPreservation
```

Il ne s'agit pas d'un renommage de la dernière relation. Le témoin annoté
`.const .punit [] → .sort 1` satisfait la simulation applicative pour toutes
les spines : au contexte vide, `pt` fournit une appartenance effectivement
transportée de `unitSet` vers `univ 1`; après la première application, la source
devient `empty`, qui se propage sous les applications suivantes. Pourtant
`unitSet ≠ univ 1`, puisque `empty` appartient à la cible mais pas à la
source. Le témoin satisfait l'enveloppe universelle et, par restriction,
l'interface des spines lisibles pour tout contexte producteur.
`readableApplicativeMembershipSimulation_strictlyWeakerThanEquality` empaquette
donc le non-converse direct et non vacue au niveau exact de cette interface.

Enfin, `aliasReadableApplicativeMembershipSimulationFails` et
`b0WAndWhnfDoNotDetermineReadableApplicativeMembershipSimulation` raccordent
cette interface exacte au contre-modèle existant : sa projection sur la spine
vide, qui est toujours lisible, donnerait la préservation gardée déjà réfutée.
Ainsi, la relation est suffisante pour les consommateurs, strictement plus
faible que l'égalité et non reconstructible depuis `B0W` sur ce dépliage
concret.

La recherche d'un générateur local aboutit à une caractérisation exacte, et
non à un nouvel étage de force. `ReadableApplicativeGenerator` ne demande à
une relation sur deux lectures annotées que deux lois : transporter
l'appartenance dans le contexte courant, puis rester fermée lorsque le même
argument effectivement lu est appliqué des deux côtés.
`LocallyGeneratedReadableSimulation` affirme seulement l'existence d'une telle
relation contenant la paire tête/corps. Les preuves établissent

```text
LocallyGeneratedReadableSimulation
        ↔
ReadableApplicativeMembershipSimulation
```

Le théorème `locallyGeneratedReadableSimulation_iff` fixe cette équivalence.
La direction locale-vers-globale est une induction sur `DenoteMetaSpine`; la
direction inverse prend comme relation la simulation lisible déjà obtenue, qui
est fermée par une lecture supplémentaire. Le témoin `.const .punit [] →
.sort 1` sépare aussi cette présentation locale de l'égalité sémantique dans
`locallyGeneratedReadableSimulation_strictlyWeakerThanEquality`, et
`aliasLocallyGeneratedReadableSimulationFails` réfute son existence depuis
`B0W` sur le même δ.

Ce résultat sépare donc proprement le **générateur local** de sa **fermeture
contextuelle**, mais ne prétend pas que les deux ont des forces logiques
différentes : à ce niveau de généralité, ils sont équivalents.

L'audit producteur isole ensuite une relation particulière qui ne mentionne ni
spine ni simulation achevée. `SemanticApplicativeSeed V before after` conserve
exactement deux déterminations locales :

```text
before ⊆ after

∀ argument,
  app before argument = app after argument
```

`DeltaHeadBodySeed` demande ce paquet entre les interprétations des deux
lectures annotées, uniformément en `ρ`. L'identité sémantique le produit, mais
la conclusion exportée est plus faible. `deltaHeadBodySeed_of_delta` montre que
le vrai `Delta` de ConLeche construit ce seed pour les lectures concrètes avant
et après dépliage ; `deltaHeadBodySeed_of_acvalDefnInst` raccorde le producteur
amont actuellement utilisé.

Cette relation est fermée localement par application. L'inclusion donne la loi
d'observation du générateur ; après un argument, l'égalité point par point rend
les deux résultats identiques, donc fournit à la fois la nouvelle observation
et la fermeture pour l'argument suivant. Ainsi :

```text
identité sémantique
        ↓
DeltaHeadBodySeed
        ↓
ReadableApplicativeMembershipSimulation
        ↓
consommateurs gardés
```

Les deux étages sont formellement séparés. Au niveau des valeurs sémantiques,
`unitSet ⊆ upair pt empty` est non vacue, les deux valeurs donnent `empty` après
toute application, mais elles ne sont pas égales :
`semanticApplicativeSeed_strictlyWeakerThanEquality` sépare donc le seed de
l'identité sans vider sa première clause. Au niveau des lectures annotées,
`deltaHeadBodySeed_strictlyWeakerThanEquality` donne aussi le non-converse.
Inversement, `readableApplicativeSimulation_strictlyWeakerThanDeltaHeadBodySeed`
construit une simulation lisible qui ne satisfait pas le seed. Ce dernier
séparateur part toutefois d'une tête interprétée par `empty` et sa simulation
est donc vacue ; il établit le non-converse formel, pas encore une stricte
séparation non vacue à cet étage.

Enfin, `aliasDeltaHeadBodySeedFails` et
`b0WAndWhnfDoNotDetermineDeltaHeadBodySeed` montrent que le même témoin `B0W`
et le même δ de l'alias ne reconstruisent pas cette relation productrice : elle
engendrerait la simulation lisible déjà réfutée.

L'audit teste ensuite la restriction suggérée par les arguments lisibles.
`ReadableDeltaSeed` conserve l'inclusion à la tête, mais ne demande l'égalité
après application que pour un `argumentReading` produit par un appel attesté de
`denoteMeta` dans le contexte producteur fixé. Les théorèmes
`DeltaHeadBodySeed.toReadableSeed`, `readableDeltaSeed_generator` et
`ReadableDeltaSeed.toReadableSimulation` établissent :

```text
DeltaHeadBodySeed
        ↓
ReadableDeltaSeed
        ↓
ReadableApplicativeMembershipSimulation
```

Le dernier converse échoue formellement dans
`readableSimulation_doesNotDetermineReadableDeltaSeed`, mais son séparateur est
encore vacue du côté des appartenances. Plus important, la première flèche ne
peut pas encore être déclarée stricte dans le cas δ pertinent.
`ReadableDeltaSeed.toDeltaHeadBodySeed_of_valuationIndependent` montre en effet
qu'à profondeur zéro la seed lisible reconstitue la seed universelle dès que
les deux lectures sont indépendantes de `ρ`. La raison est constructive : une
`fvar` est lue comme `.bvar 0`, puis sa valeur sous `ρ` peut être choisie comme
n'importe quel argument sémantique. Le seul succès brut de `denoteMeta` ne
définit donc pas une classe sémantiquement restreinte d'arguments pour des têtes
closes.

Le producteur, en revanche, est réellement factorisé. La nouvelle interface
`AcvalDefnReadableSeed` porte uniquement la relation lisible entre la lecture de
la constante stockée et celle de son corps instancié. Le théorème
`readableDeltaSeed_of_acvalDefnReadableSeed` ouvre le vrai
`unfoldDefinition`, récupère le même spine syntaxique et ses mêmes lectures,
puis propage cette relation jusqu'aux lectures complètes. Sa preuve n'appelle
ni `Delta` ni une égalité des annotations complètes. L'invariant existant
`AcvalDefnInst` construit cette interface dans
`acvalDefnReadableSeed_of_acvalDefnInst`; le raccord composé
`readableDeltaSeed_of_acvalDefnInst_withoutDelta` évite donc le théorème
`Delta`, même si l'implémentation actuelle de `AcvalDefnInst` fournit toujours
l'identité exacte au niveau tête/corps.

Enfin, `aliasReadableDeltaSeedFails`,
`b0WAndWhnfDoNotDetermineReadableDeltaSeed` et
`oldSlice_hasNoAcvalDefnReadableSeed` montrent respectivement que la relation
lisible, sa reconstruction depuis `B0W + δ`, et le contrat producteur affaibli
sont tous impossibles sur le même contre-modèle.

Le test suivant n'introduit pas une nouvelle variante de « lisible ». Il indexe
la capacité par l'occurrence δ elle-même. Dans `DeltaSpineAdmission`, la lecture
`DenoteMetaSpine` fixe la liste ordonnée `source.getAppArgs`, tandis que
`WScoped` et `CtxOk` sont certifiés pour chaque argument de cette même liste. Le théorème
`deltaSpineAdmission_of_sourceRead` reconstruit exactement ce paquet depuis la
lecture, la portée et le contexte du terme source. Ces deux dernières
conditions certifient l'admissibilité opérationnelle de l'occurrence ; elles ne
sont pas transformées artificiellement en prémisses sémantiques.

`SemanticDeltaSpineSeed` demande alors uniquement ce que cette spine finie
consomme. Sur une spine vide, il conserve l'inclusion de la tête. Sur une spine
non vide, il ajoute l'égalité après le premier argument sémantique réellement
présent. Les applications restantes sont identiques des deux côtés et propagent
cette égalité par congruence.
`SemanticApplicativeSeed.toDeltaSpineSeed` formalise directement la restriction
de la seed universelle à toute spine sémantique finie ; les raccords annotés
`DeltaHeadBodySeed.toAdmissibleDeltaSeed` et
`ReadableDeltaSeed.toAdmissibleDeltaSeed` font la même projection sur
l'occurrence attestée. `AdmissibleDeltaSeed` impose ce paquet pour toute
valuation `ρ`, sur les lectures exactes de l'occurrence, et
`AdmissibleDeltaSeed.toGuardedMembershipPreservation` restitue la préservation
gardée sur le terme δ complet.

Cette restriction produit cette fois une réduction stricte et non vacue au
niveau sémantique. Dans
`semanticDeltaSpineSeed_strictlyWeakerThanUniversalSeed`, la spine testée est
vide : `unitSet` et `upair pt (kpair empty pt)` partagent effectivement le
membre `pt`, donc l'inclusion exigée n'est pas vide, mais leurs applications à
`empty` diffèrent. La seed de l'occurrence est satisfaite tandis que la seed
universelle `SemanticApplicativeSeed` est réfutée. Cette séparation porte sur
une occurrence sans argument ; elle ne prétend pas encore séparer les deux
notions sur toute spine non vide.

Le raccord producteur est également direct.
`admissibleDeltaSeed_of_acvalDefnReadableSeed` ouvre le vrai
`unfoldDefinition`, retrouve les lectures des deux têtes et la même liste
d'arguments, construit leur `DeltaSpineAdmission`, puis produit la seed de
l'occurrence depuis `AcvalDefnReadableSeed`. Il n'utilise pas une égalité des
lectures complètes. Enfin, `aliasDeltaSpineAdmission`,
`aliasAdmissibleDeltaSeedFails` et
`b0WAndWhnfDoNotDetermineAdmissibleDeltaSeed` montrent que, sur le δ concret de
l'alias à spine vide, `B0W` ne reconstruit même pas cette interface restreinte :
son unique inclusion de tête est déjà fausse.

Le weakening supplémentaire vient donc bien de l'admissibilité constitutive
d'un **usage effectivement présent** — sa spine finie et sa position — plutôt
que du seul fait qu'un argument possède une lecture. La portée et le contexte
fixent honnêtement cette occurrence ; ils ne suffisent pas, à eux seuls, à
produire le transport sémantique.

L'audit β a ensuite été développé indépendamment de la référence δ gelée au
commit `d296630`, sans importer d'interface d'audit propre à δ.
`OperationalOccurrence` conserve le disjoint β exact de `whnf_app_inv` : la
tête lambda, le run du corps instancié et l'autorisation acceptée par le
checker. `SemanticConsequence` ne conserve que l'égalité entre redex et réduit
et la bonne dénotation du réduit.

La branche de genre zéro se factorise par une seule capacité sémantique gardée :

```text
genre = 0 → interprétation(argument) ∈ interprétation(domaine).
```

La branche où la gate se déclenche la construit en rendant `genre = 0`
impossible. Dans la branche certifiée, `InferClaimIOS` établit l'appartenance au
type inféré de l'argument ; `DefEqClaim` est ensuite affaibli successivement
vers le transport uniforme des appartenances puis vers l'appartenance de
l'argument concret au domaine concret. Cette dernière ligne est aussi le seul
résultat de l'égalité utilisé par les preuves d'inférence d'application complète
et IO. La même ligne affaiblie alimente donc trois consommateurs réels, tandis
que β lui-même n'en consomme que la forme gardée.

Lean sépare directement quatre forces :

```text
égalité sémantique
        ↓ strictement
transport uniforme des appartenances
        ↓ strictement
appartenance de l'argument de l'occurrence à son domaine
        ↓ strictement lorsque le genre de la lambda est conservé
obligation β exacte de genre zéro
```

Sur une occurrence β de genre zéro réellement acceptée, le contre-modèle `B0W`
existant construit l'appartenance au type inféré mais réfute l'accord
sémantique, le transport uniforme, l'appartenance concrète au domaine et donc
l'obligation β gardée exacte. La première dépendance résistante est ainsi le
transport sémantique du type inféré accepté par le checker vers le domaine
stocké de la lambda, et non l'inférence de l'argument elle-même.

L'analyse β est ainsi stabilisée indépendamment : la capacité réutilisable du
côté producteur est le transport uniforme des appartenances, tandis que
l'appartenance concrète au domaine et sa garde par le genre sont les projections
strictement plus faibles consommées en aval. Cela ne démontre ni une minimalité
globale, ni sa persistance dans un futur invariant, ni l'atteignabilité du
contre-modèle depuis l'environnement vide, ni un facteur commun minimal avec
δ. Le fichier β autonome
recompile contre le commit ConLeche épinglé, ne contient ni `sorry`, ni `axiom`
explicite, ni `Classical`, ni `native_decide`, et porte le SHA-256
`709169dc75e510985a1501f2366b70f777ae88adf714ab84aaf7670f4bbcb9bf`.
Son audit axiomatique ne rapporte que `propext`, `Classical.choice` et
`Quot.sound`, hérités du développement ConLeche épinglé.

Ce n'est qu'après stabilisation indépendante des deux analyses qu'un module de
comparaison séparé a importé leurs interfaces complètes sans modifier leurs
sources. Le théorème `betaTransport_iff_deltaGuarded` démontre que le transport
uniforme défini indépendamment pour β et la préservation gardée des appartenances
extraite de δ sont définitionnellement le même prédicat lorsque contexte, source
et cible coïncident. La seed δ d'occurrence déjà établie se projette en outre
vers ce prédicat, tandis que celui-ci, joint à l'appartenance source produite
indépendamment, restitue la ligne concrète argument/domaine de β. La structure
partagée est donc la règle gardée de transport, non les détails opérationnels
des producteurs ni le jugement particulier de chaque consommateur.

La comparaison fournit maintenant aussi un non-converse direct et non vacue au
niveau de ces deux prédicats. `strictnessDeltaSource_unfolds` fixe une vraie
source δ à un argument avec sa spine inchangée. Sur la même spine admise,
`strictnessCommonCapacity` transporte le membre réel `ptTag`, tandis que
`strictnessDeltaOccurrenceSeed_fails` réfute la seed d'occurrence : sa clause
d'observation de la tête placerait `ptTag` dans une lambda du régime graphe. Le
théorème `commonCapacity_doesNotReconstruct_deltaOccurrenceSeed` démontre donc,
dans la classe non restreinte des indices concordants,

```text
GuardedMembershipPreservation
        ↛
AdmissibleDeltaSeed.
```

L'interface de seed δ d'occurrence est ainsi strictement plus forte que le
prédicat de transport commun dans cette classe ; du côté β, le prédicat commun
est exactement le transport intermédiaire extrait indépendamment. Le séparateur
conserve toutefois une frontière explicite : sa source opérationnelle et sa
spine non vide sont réelles, mais ses deux lectures sémantiques de tête sont
choisies indépendamment d'`AcvalDefnInst`.

Le test restreint au producteur est maintenant fermé dans la direction opposée.
`acvalDefnInst_constructs_commonAndOccurrenceSeed` démontre que, pour tout
dépliage δ réel muni de ses lectures source et cible effectives, de sa portée et
de son certificat de contexte, `AcvalDefnInst` construit une seed d'occurrence
concordante, puis sa projection gardée commune. Par conséquent,
`acvalDefnInst_excludes_commonWithoutOccurrenceSeed` exclut un cas réellement
produit où le transport commun serait vrai tandis que toute seed d'occurrence
concordante serait fausse. Cela ne démontre **pas** que le prédicat commun seul
reconstruit la seed. Cela démontre quelque chose de propre au producteur actuel
de ConLeche : ses hypothèses reconstruisent déjà l'interface plus forte sans
consommer le prédicat commun.

Il faut donc distinguer l'ordre logique de l'ordre relatif au producteur :

```text
prédicats non restreints :
AdmissibleDeltaSeed > GuardedMembershipPreservation

sorties réelles d'AcvalDefnInst :
AcvalDefnInst → AdmissibleDeltaSeed → GuardedMembershipPreservation
```

Aucune minimalité dans une classe `K`, aucune persistance et aucune
atteignabilité depuis l'environnement initial ne sont démontrées. Le fichier de
comparaison ne contient aucune construction interdite, porte le SHA-256
`e28b68ac45439ce8e377e16d16dc5ad2de0e0ac4c82b0d613ea0c78394df97fb`,
et son audit axiomatique rapporte à nouveau seulement les trois dépendances
héritées de ConLeche.

L'audit ι a ensuite été lancé indépendamment des interfaces δ et β, sans
anticiper de capacité commune. `OperationalOccurrence` conserve l'occurrence
exacte exposée par `iotaRec_inv`, puis `FiredRuleSelection` ne retient que le
récursionneur stocké, la règle effectivement sélectionnée et le fait qu'elle
se déclenche. `recRuleLaw_of_selection` marque séparément l'entrée de
`RecRules`, tandis que `SemanticConsequence` et `ContinuationCertificate`
distinguent la loi sémantique du résultat des garanties nécessaires à la
poursuite du calcul.

Le premier test `.plain` construit un environnement explicite muni d'un vrai
témoin `B0W`. Un récursionneur stocké y possède une règle opérationnellement
admissible dont le RHS est `PUnit PUnit.unit`. `badPlainRun` démontre que
`iotaRecFueled` sélectionne et exécute réellement cette règle en mode
`verified`. `badContinuationCertificate` établit indépendamment que le réduit
est bien scopé, fermé, borné dans ses feuilles et compatible avec le contexte
vide. La continuation ne manque donc pas.

La loi sémantique, en revanche, ne se reconstruit pas. `badRhsReading` fixe la
lecture exacte du RHS. `badRhsHeadWellDenoted` et
`badRhsArgumentWellDenoted` montrent que ses deux constituants sont chacun
bien dénotés. Mais `badRhsHeadNotInPi` réfute, pour tout `v`, `A` et `B`,
l'appartenance de la lecture de `PUnit` à `piR v A B` : au niveau zéro un
habitant devrait être `pt`, tandis qu'au niveau positif il devrait être un
graphe, ce que `unitSet` ne peut être. `badRhsApplicationFrameFails` en déduit
l'impossibilité du paquet relationnel partagé exigé par `WellDenoted_app`, sans
consommer ni l'appartenance de l'argument au domaine ni la condition de niveau
zéro.

Ainsi `badPlainRhsWellDenotedFails`, `badRecRulesFails` et
`badPlainOperationalSemanticSeparator` établissent ensemble :

```text
B0W + sélection .plain + exécution ι réelle + continuation
        ↛
bonne dénotation du RHS sélectionné.
```

La première coupure interne est relationnelle : la validité individuelle des
constituants ne détermine pas leur composabilité sémantique. Ce séparateur ne
montre pas que les autres clauses de `WellDenoted_app` sont inutiles en
général, ne traite pas encore `.nested` et ne revendique pas l'atteignabilité
de son environnement depuis l'environnement initial. Les deux fichiers ι
recompilent contre le commit ConLeche épinglé et portent respectivement les
SHA-256
`dd4b0f4dd7853eb637d19b350d0375f288f6607d399a0ab9901d8c3e40f24449`
et
`4d91808724ed2b25b030032fe8d0795a04d51c2a5d4ae02efc7c9a5c48a5ddbe`.
Ils ne contiennent ni `sorry`, ni `axiom` explicite, ni `Classical`, ni
`native_decide`; leurs audits rapportent seulement `propext`,
`Classical.choice` et `Quot.sound`, hérités de ConLeche.

Ces résultats ne portent pas encore sur toutes les familles de jugements
sémantiques, ne caractérisent aucune relation minimale et ne justifient aucune
persistance dans `B1`. Ils ne montrent ni que `AcvalDefnInst` peut être remplacé
dans ConLeche sans modifier l'invariant amont, ni que la seed admissible est
minimale, ni que le contre-modèle est atteignable depuis l'environnement vide.

Conformément à la règle d'arrêt, ni la ligne `WellDenoted` de l'argument de
l'application extérieure ni son existentiel propositionnel portant le frame
partagé n'ont été testés. Le témoin antérieur
reste arbitraire dans la classe `B0W` ; son atteignabilité depuis
l'environnement vide n'est pas revendiquée.

Ainsi, `Q0` n'est pas l'unique obligation supplémentaire d'une factorisation
uniforme depuis des témoins `B0W` arbitraires. Conformément à la règle d'arrêt,
`thm` et `opaque` n'ont pas été testés, aucune capacité historique `H` n'a été
proposée et aucun `B1` n'a été introduit. Le second état antérieur est un témoin
admissible de `B0W` ; ce test n'affirme pas qu'il est atteignable depuis
l'environnement vide par une exécution ConLeche. `Pdenote` expose désormais la
ligne défaillante comme une obligation transitionnelle et
`pdenoteSeparator` empaquette les mêmes données concrètes sous la forme
`Nonempty (Separator B0W Pdenote)`. L'ombre propositionnelle est nécessaire
parce que le run du checker et son fuel sont obtenus propositionnellement ;
elle n'ajoute aucune revendication scientifique. L'adaptateur autonome reproduit
l'interface générique pertinente sans rendre les deux dépôts dépendants l'un de
l'autre. Le fichier externe recompile contre le commit épinglé, ne contient ni
`sorry`, ni `axiom` explicite, ni `native_decide`, et porte le SHA-256
`2709bd20f263cb6981860b690b944a1b32fb74d04089929ab9c9197360b7546c`.

Références épinglées pour l’étude :

- [théorème principal](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/MainTheorem.lean) ;
- [réécriture des projections](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/Frontend/ProjRec.lean) ;
- [point d’application dans le frontend](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/Frontend/ExportC.lean) ;
- [hypothèse en théorie des ensembles](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/OVERVIEW.md#7-the-set-theory-assumption) ;
- [limites du théorème](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/OVERVIEW.md#9-what-the-theorem-does-not-cover).

## 3. Chaîne de formation

`VerificationPipeline` distingue quatre carriers et trois transformations :

```text
Source
  │ exportStep
  ▼
Exported
  │ parseStep
  ▼
Parsed
  │ prepareStep
  ▼
Presented
```

`Accepted : Presented → Type` reste extérieur au pipeline. Définir les trois
fonctions ne construit donc aucune fidélité.

`VerificationFidelity` introduit séparément :

```text
FaithfulExport
FaithfulParse
FaithfulPrepare
```

`FaithfulRun` rassemble les trois témoins appliqués aux occurrences
effectivement calculées. `FaithfulComp` les compose par une somme dépendante qui
conserve les intermédiaires. Le certificat `ConstitutivelyAccepted` exige alors
deux champs irréductibles l’un à l’autre : un `FaithfulRun` et une acceptation
terminale.

## 4. Séparateur acceptation / origine

Le pipeline `collapsedPipeline` transforme les deux occurrences distinctes de
l’histoire `Separators.twoStepHistory` en une valeur terminale unique de type
`Unit`. Cette valeur est acceptable dans le modèle terminal abstrait.

Une réalisation fidèle des occurrences exigerait cependant une
`InjectiveMap` vers `Unit`. Le théorème existant
`Separators.noFaithfulTerminalOnlyRealization` la réfute. Le nouveau théorème
`acceptedPresentation_doesNotDetermineOrigin` réemploie directement ce
séparateur : l’acceptation terminale ne reconstruit pas l’identité des
occurrences amont.

## 5. Factorisation suffisante du transport `no False`

Pour une famille de contre-exemples `Counterexample : Occurrence → Type`, le
module définit :

```text
NoCounterexample Counterexample
```

Deux obligations suffisent au transport négatif abstrait :

1. `SourceCoverage` fournit une occurrence présentée pour toute occurrence
   source pertinente ;
2. `PreservesCounterexample` transforme tout contre-exemple source en
   contre-exemple présenté correspondant.

Le théorème `transportNoCounterexample` construit alors :

```text
aucun contre-exemple présenté
  → aucun contre-exemple source
```

La nécessité des deux composantes est testée séparément :

- `coverage_isNecessary` utilise une source habitée et un carrier présenté vide ;
- `counterexamplePreservation_isNecessary` conserve une couverture totale mais
  rend impossible le transport du contre-exemple.

Il s’agit d’une minimalité relative à cette propriété et à cette famille finie
d’obligations, non d’une minimalité absolue sur toutes les représentations.

## 6. Cas de la réécriture de projection

Au commit étudié, le frontend de ConLeche reconnaît certaines fonctions dont le
corps est une projection primitive et remplace ce corps par une application du
recursor. Au niveau du record poussé ensuite, le nom, la position dans le flux,
le contexte antérieur pertinent et le type déclaré restent inchangés ; le corps
est remplacé.

`ConLecheProjectionCase` reconstruit localement cette forme :

- `LocatedDeclaration` individue une déclaration et son contexte ;
- `rewriteProjection` ne modifie que `body` ;
- `ProjectionRewriteWitness` conserve explicitement le nom, la position, le
  préfixe et le type, et atteste la nouvelle forme du corps ;
- `projectionNoFalseTransport` transporte l’absence de déclaration de type
  `False`.

Cette reconstruction est un modèle local du contrat observable de la
transformation documentée. Elle n’est ni une copie du frontend ni une preuve
portant sur tout son code.

La minimisation apporte ensuite une distinction supplémentaire.
`metadataErasureNoFalseTransport` montre que, pour la seule propriété abstraite
`no False`, le nom, la position, le préfixe et le corps peuvent être oubliés
ensemble si le type déclaré et la couverture restent conservés. Ces données
peuvent néanmoins demeurer nécessaires pour établir concrètement la fidélité de
l’implémentation réelle.

À l’inverse, `substitutedType_hasNoFaithfulRewrite` construit une mutation du
type déclaré et réfute le témoin riche de réécriture, même lorsque le modèle
terminal abstrait accepte encore l’objet. Le type n’est donc pas oubliable pour
le transport étudié.

## 7. Audit externe reproductible

Le script [`scripts/run_con_leche_audit.py`](../../scripts/run_con_leche_audit.py)
fixe les racines exportées :

```text
StrongPerimetralTurning Cycle2 ConstitutiveAlignment
```

Il vérifie le commit et la propreté de l’arbre en mode confirmatoire, construit
le dépôt, contrôle le manifeste, régénère l’export, calcule son empreinte avant
et après le checking, puis exécute exactement :

```text
con-leche --verified --jobs=1 FILE.ndjson
```

Seuls le code de sortie `0` et la ligne exacte
`accepted N declarations (--verified)` ferment l’exécution. Les clones, builds
externes, exports et journaux restent hors du dépôt.

Exemple Windows :

```powershell
py -3 scripts/run_con_leche_audit.py `
  --lean4export C:\external\lean4export\.lake\build\bin\lean4export.exe `
  --lean4export-source C:\external\lean4export `
  --lean4export-commit COMMIT_40_HEX `
  --con-leche C:\external\con-leche\.lake\build\bin\con-leche.exe `
  --con-leche-source C:\external\con-leche `
  --con-leche-commit COMMIT_40_HEX `
  --output-dir C:\external\audit-output `
  --confirmatory `
  --expected-head COMMIT_DU_DEPOT_40_HEX
```

## 8. Run exploratoire de compatibilité

Un premier run a fermé la question de compatibilité pratique pour le socle
antérieur à ce module. Son statut reste `exploratoire`, car il ne visait pas un
commit contenant le présent chantier.

```text
commit du dépôt : 794b8185abba13eb4ab91f77a7c87fd1cd2d6ae0
Lean du dépôt : v4.33.1, 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
lean4export : 411dce7db58a3afc60ecab2d211acd1042b593dc
ConLeche : 86cd20a65660d757cedc81561a44579099b565d0
mode : --verified --jobs=1
taille de l’export : 375004155 octets
SHA-256 avant et après : 7622cc2e2b40f2f3341381f3d0f79e8d94599348e73637410a01a690cdfcc74d
verdict : accepted 63916 declarations
code de sortie : 0
```

Ce run montre que ConLeche construit avec Lean `v4.33.0` accepte cet export
produit avec Lean `v4.33.1`. Il ne remplace pas le run confirmatoire qui devra
porter sur le commit scientifique final du chantier.

Après ajout du noyau réduit et de ses séparateurs, un second run exploratoire
sur la copie de travail a accepté `64359` déclarations. L’export mesurait
`376371840` octets ; son SHA-256 est resté
`61c4e260bf3740b068c5c57cb53f3da672c1b43e86e11ebcc80d59958ef9d052`
avant et après le checking. Le rapport externe porte l’empreinte
`655c9dbfcc587138c196549f9c4f5e25cb0745b22d286f8a11be4f35b68caf90`.
Son statut reste exploratoire parce que le chantier n’est pas encore commité.

## 9. Portée exacte

La partie Lean démontre constructivement :

- la séparation formation/fidélité/acceptation ;
- la séparation soundness/completeness/provenance dans le contrat `R → S` ;
- la suffisance de la projection terminale
  `{base2, type_reads, mem_type}` du véritable `EnvModelM` ;
- une construction positive du témoin vide consommé par le capstone ;
- la descente de l'extraction terminale vers l'ombre propositionnelle ;
- le passage de la stabilité historique à la stabilité faible ;
- la réfutation par séparateur d'une reconstruction locale et des stabilités
  historiques assez fortes pour la produire ;
- la localisation, dans le séparateur ConLeche externe, de l'échec au seul
  accord sémantique entre type inféré et type déclaré ;
- la suffisance de cet accord `Q0` pour reconstruire les deux lignes locales de
  la transition concrète, les deux autres faits étant construits séparément ;
- un second séparateur montrant qu'un témoin `B0W` arbitraire avec une
  transition `defn` acceptée ne reconstruit pas `valueWellDenoted` ;
- son empaquetage comme `Pdenote` indexé par la transition et comme
  `Separator` générique propositionnellement habité ;
- la reconstruction des lectures de la tête et de l'argument d'une sortie
  applicative depuis `base2` et le seul `ValueFrontRun`, sans consommer les
  autres composantes de la slice terminale, eta ou `ConstantValRun` ;
- un troisième séparateur montrant que ces lectures, le même `ValueFrontRun` et
  un témoin `B0W` ne déterminent pas `WellDenoted` pour la tête annotée ;
- sa localisation interne : le domaine de la lambda, la tête constante de son
  corps applicatif et l'argument annoté sont bien dénotés, tandis que la seule
  clause `headInPiR` du frame partagé est déjà constructivement impossible ;
- la factorisation positive de `headInPiR` par une appartenance `M`, un accord
  de réduction `R` portant sur le même type inféré et la lecture exacte du même
  `forall` réduit ; dans le contre-modèle, `M` est construit et `R` est réfuté ;
- la factorisation locale de `R` dans la branche δ par l'égalité des lectures
  avant et après le dépliage concret ; `Delta` et `AcvalDefnInst` suffisent à la
  produire, tandis qu'un témoin `B0W` et le `whnf` accepté ne la déterminent
  pas dans le contre-modèle ;
- l'affaiblissement de `R` vers le transport orienté de l'appartenance de la
  tête précise ; pour cette occurrence où `M` est déjà construit, ce transport
  est équivalent à `headInPiR` et ne constitue donc pas encore un intermédiaire
  strict ;
- une réduction réellement stricte de l'égalité sémantique uniforme vers la
  préservation uniforme de tous les jugements d'appartenance : l'égalité
  implique ce transport, ce transport restitue le `headInPiR` particulier, et
  un second dépliage δ concret satisfait ce transport de façon non vacueuse
  tout en réfutant l'égalité ;
- sur le contre-modèle de l'alias, la non-reconstructibilité de cette capacité
  uniforme depuis un même témoin `B0W`, le `whnf` concret et la lecture exacte
  de son résultat ;
- l'affaiblissement transversal vers la préservation gardée par `Sat`, qui
  remplace l'égalité dans les consommateurs réels `SortSemAt`, `SortSemAtIO` et
  `StructEtaIrrel`, et reste non reconstructible depuis `B0W` sur le même
  dépliage dans le contexte vide ;
- le non-converse direct et non vacue entre cette préservation gardée et
  l'égalité, puis la chaîne productrice δ
  `AcvalDefnInst → Delta → identité de lecture → préservation gardée` ;
- l'extraction formelle de la classe de spines de `delta_core` : toute liste
  finie `source.getAppArgs`, inchangée et réappliquée dans le même ordre au
  corps instancié, sans prémisse sémantique à cette couche ;
- la caractérisation locale/globale de la simulation sur ces spines lisibles :
  une relation qui transporte l'appartenance immédiatement et reste fermée par
  chaque argument effectivement lu engendre exactement la simulation lisible ;
  cette présentation est strictement plus faible que l'égalité mais équivalente
  à sa propre fermeture contextuelle, et demeure irréconstructible depuis
  `B0W` sur le séparateur δ ;
- l'extraction productrice de `DeltaHeadBodySeed`, constitué seulement de
  l'inclusion à la tête et de l'accord après une application sémantique : le δ
  réel le construit, il engendre la simulation lisible, un séparateur non vacue
  le distingue de l'identité au niveau sémantique, un autre non-converse le
  distingue formellement de la simulation lisible, et le contre-modèle de
  l'alias interdit sa reconstruction depuis `B0W` ;
- l'essai contrôlé `ReadableDeltaSeed` : sa relation tête/corps suffit et se
  propage dans le spine exact depuis un contrat producteur plus faible que
  `Delta`, mais le succès brut de `denoteMeta` ne restreint pas encore les
  arguments sémantiques pour des lectures closes ; une `fvar` à profondeur zéro
  reconstitue alors l'universalité de `DeltaHeadBodySeed`, tandis que le même
  alias réfute la seed lisible et son contrat producteur depuis `B0W` ;
- la restriction suivante à l'occurrence δ effectivement admise :
  `DeltaSpineAdmission` lie lecture, portée et `CtxOk` aux positions exactes de
  `source.getAppArgs`, tandis que `SemanticDeltaSpineSeed` ne conserve que
  l'inclusion de tête et, si la spine n'est pas vide, l'accord après son premier
  argument réel ; cette seed suffit à la préservation gardée du terme complet,
  un séparateur non vacue à spine vide la distingue de la seed universelle, le
  producteur affaibli la construit directement, et le même alias interdit
  encore sa reconstruction depuis `B0W` ;
- une factorisation β indépendante depuis l'occurrence acceptée exacte vers sa
  conséquence sémantique, par l'obligation gardée d'appartenance au domaine au
  genre zéro produite par le partage gate/certificat ;
- les affaiblissements stricts de l'égalité sémantique type inféré/domaine vers
  le transport uniforme des appartenances, puis l'appartenance concrète de
  l'argument au domaine, et enfin l'obligation gardée consommée par β ; la
  ligne non gardée est aussi le résultat exact dépendant de l'égalité dans les
  inférences d'application complète et IO ;
- un séparateur β de genre zéro réellement accepté sur lequel l'appartenance au
  type inféré est vraie mais toutes les relations ultérieures de cette chaîne
  sont réfutées depuis `B0W` ;
- une comparaison formelle postérieure démontrant que le transport β extrait
  indépendamment et la préservation gardée δ coïncident définitionnellement à
  indices identiques, que la seed δ d'occurrence se projette vers cette
  relation partagée et que celle-ci, jointe à l'appartenance source, fournit le
  jugement de l'occurrence β ;
- un séparateur direct et non vacue sur une spine δ admise, fixée et non vide :
  le transport gardé commun conserve `ptTag`, tandis que la seed d'occurrence
  est impossible ; cela démontre le non-converse au niveau des prédicats,
  tandis que ce séparateur lui-même ne porte pas sur les têtes sémantiques
  produites par `AcvalDefnInst` ;
- la fermeture de cette question restreinte au producteur dans la direction
  opposée : les données d'un dépliage δ réel jointes à `AcvalDefnInst`
  construisent toujours une seed d'occurrence concordante et sa projection
  commune, ce qui exclut un séparateur transport-commun-sans-seed dans cette
  classe sans affirmer que le seul prédicat commun reconstruit la seed ;
- une factorisation ι indépendante séparant l'occurrence opérationnelle, la
  sélection de la règle stockée, la loi sémantique fournie par `RecRules` et le
  certificat de continuation ;
- un séparateur `.plain` sur une exécution réelle de `iotaRecFueled` : le témoin
  `B0W` et toutes les garanties de continuation sont construits, les deux
  constituants du RHS sont bien dénotés, mais la lecture de sa tête n'appartient
  à aucun `piR`, ce qui réfute le frame applicatif partagé, la bonne dénotation
  du RHS et la loi `RecRules` correspondante ;
- la composition sans effacement des occurrences intermédiaires ;
- un séparateur d’origine réutilisant le noyau du Cycle 1 ;
- la suffisance de la couverture et de la conservation des contre-exemples ;
- leurs séparateurs négatifs indépendants ;
- la fidélité du modèle local de réécriture ;
- l’oubli admissible des métadonnées non typales pour `no False` ;
- le rejet d’une substitution du type déclaré.

Elle ne démontre pas la fidélité complète de `lean4export`, du parser ou du
frontend de ConLeche. Le run externe reste une observation reproductible. La
garantie de ConLeche reste relative à son hypothèse de modèle en théorie des
ensembles. Elle ne construit pas encore la slice terminale directement depuis
`FullyChecked` : l'induction disponible transite par le carrier complet. Le
deuxième et le troisième séparateurs réfutent des implications uniformes depuis
des témoins `B0W` arbitraires ; ils n'établissent pas que leur état antérieur
soit atteignable depuis l'environnement vide par le checker. Enfin,
l'acceptation par ConLeche ne
remplace pas les audits `#print axioms` du dépôt : ceux-ci
établissent séparément que nos théorèmes principaux ne dépendent d'aucun axiome.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d’OpenAI, sous direction humaine et au cours
> d’interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
