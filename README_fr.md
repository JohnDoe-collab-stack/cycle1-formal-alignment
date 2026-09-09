# Cycle 1 — Preuve formelle d'alignement relatif

[English](README.md) | **Français**

> **Déclaration de génération par IA.** Le responsable du projet déclare que
> chaque élément de ce dépôt a été écrit de A à Z par des modèles de la série
> ChatGPT d'OpenAI, sous la direction d'un humain et au cours d'interactions
> successives. Voir la
> [déclaration bilingue complète](AI_AUTHORSHIP.md).

> **Ce projet construit et vérifie en Lean un noyau dépendamment typé pour
> l'alignement relatif.** Il sépare formellement la construction, la réalisation
> fidèle, l'admission par un régime opérationnel et la satisfaction d'une norme
> définie indépendamment de ce régime. Dans l'instance circulaire, il démontre que
> la norme et le régime acceptent exactement les mêmes histoires. Il construit
> ensuite une continuation minimale qui reste exactement réalisable sous toute
> implémentation concrète conforme à l'interface, mais qui est rejetée par le
> régime et par la norme. Le résultat établit ainsi que la capacité de continuer
> et la fidélité locale n'impliquent pas l'alignement normatif global, tout en
> localisant précisément le point où celui-ci est perdu.

## Contribution centrale

Pour une présentation circulaire `P` et une histoire constituée `H`, le
développement distingue trois familles de témoins:

```text
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

`F_A(H)` affirme la réalisation concrète exacte de `H` dans une algèbre `A`.
`R(H)` exprime son admission par le régime opérationnel. `S(H)` exprime sa
satisfaction d'une norme définie sans faire référence à `CircularRefinement`.

La preuve ferme la comparaison entre `R` et `S` dans les deux directions:

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

Le régime et la norme classent donc exactement les mêmes histoires. Il s'agit
d'un accord extensionnel sur leurs carriers: leurs structures de témoins peuvent
contenir des données différentes et ne sont pas identifiées entre elles.

## Norme indépendante et mécanisme de classification

La norme circulaire combine une obligation locale et une obligation
trajectorielle:

```text
CircularSpecificationSatisfaction P H
  ├─ local : ExactNonClosingRealization P H
  └─ trajectory :
       StrictConstitutivePrefix (perimeterDeployment P) H
       → P.TotalLoop
```

La première composante exige que chaque exigence non fermante soit réalisée par
une occurrence constituée qui lui corresponde exactement. La seconde donne son
sens trajectoriel à la fermeture: toute continuation stricte au-delà du
déploiement périmétral devrait réaliser une boucle totale.

La complétude des carriers suit la chaîne constructive suivante:

```text
S(H)
  ↓ réalisation locale exacte
PerimeterExtension P H
  ↓ décomposition de la continuation
continuation racine
  → H = perimeterDeployment P

continuation positive
  → StrictConstitutivePrefix (perimeterDeployment P) H
  → P.TotalLoop
  → contradiction avec rejectTotalLoop
```

La branche positive est impossible. Toute histoire satisfaisant la norme est
donc exactement le déploiement canonique. La complétude du régime transporte
ensuite le raffinement circulaire canonique le long de cette égalité.

## Théorèmes centraux certifiés

Soundness du régime:

```lean
StrongPerimetralTurning.circularRefinement_soundSpecification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CircularSpecificationSatisfaction P history
```

Complétude des carriers:

```lean
StrongPerimetralTurning.CircularSpecificationSatisfaction.eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    history = perimeterDeployment P
```

Complétude du régime:

```lean
StrongPerimetralTurning.circularSpecification_complete
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    CircularRefinement P history
```

La seconde déclaration classe d'abord le carrier comme déploiement périmétral
canonique. La troisième transporte ensuite le témoin canonique du régime; elle ne
reconstruit pas automatiquement les témoins internes du régime à partir de la
norme.

## Sortie minimale diagnostiquée

Le candidat canonique de sortie est:

```text
h⁺ := oneStepAfterPerimeter P
```

Ce même objet porte simultanément les résultats suivants:

```text
StrictConstitutivePrefix (perimeterDeployment P) h⁺    habité
ExactNonClosingRealization P h⁺                        habité
ordre et adjacence canoniques                          conservés
ExactConcreteRealization A h⁺                          habité pour toute A fournie
CircularRefinement P h⁺                                réfuté
CircularSpecificationSatisfaction P h⁺                 réfuté
```

La réfutation normative est directe. La continuation stricte transforme
l'obligation trajectorielle en `P.TotalLoop`, que l'obstruction constitutive de
la présentation rejette. Elle ne dépend donc pas préalablement du rejet par le
régime.

La construction reste pourtant possible et fidèlement interprétable. La sortie
de régime ne détruit ni l'histoire produite, ni ses occurrences, ni les accords
structurels déjà conservés. Elle localise une rupture de statut normatif sur le
même objet constitué.

L'uniformité est portée par `oneStepUniformPerimetralRegimeExit`: le candidat est
fixé avant le choix de l'implémentation, puis une réalisation exacte de cette
même histoire est construite pour toute `ConcreteContinuationAlgebra P` fournie.
La frontière diagnostiquée ne dépend donc pas d'une représentation concrète
particulière conforme à l'interface.

## Utilité pour l'alignement

Le résultat formalise plusieurs séparations indispensables à un diagnostic
d'alignement:

```text
capacité à poursuivre une construction
  ≠ admission normative de cette continuation

fidélité locale, ordre et adjacence corrects
  ≠ satisfaction d'une obligation trajectorielle globale

réalisation concrète exacte
  ≠ appartenance au régime évalué
```

Un comportement localement correct ou une implémentation fidèle ne constitue
donc pas, à lui seul, un certificat d'alignement global. Le cadre rend auditables
séparément:

1. la norme imposée à une histoire;
2. le régime opérationnel censé l'appliquer;
3. la fidélité de ses réalisations concrètes;
4. la soundness et la complétude de l'accord entre norme et régime;
5. le premier candidat qui conserve la réalisation mais perd le statut normatif.

L'alignement relatif devient ainsi une relation formelle entre une spécification
autonome et un régime, évalués sur les mêmes objets constitués, plutôt qu'une
identification implicite entre ce qui peut être produit et ce qui doit être
admis.

## OOD structurel relatif au régime

Le cadre introduit l'**OOD structurel relatif à un régime** comme extension
conceptuelle du raisonnement out-of-distribution. L'OOD statistique concerne la
sortie d'une distribution de données. L'OOD structurel concerne plutôt un
candidat qui reste engendré par la construction considérée, mais n'est pas
admis par un régime explicite. Il ne requiert ni distribution de probabilité ni
jeu d'entraînement. La réalisabilité fidèle n'appartient pas à cette définition
documentaire; elle constitue une propriété supplémentaire démontrée pour le
témoin circulaire ci-dessous.

L'instance circulaire en fournit un témoin vérifié mécaniquement:

```text
h⁺ : RootedGeneratedHistory P
∀ A : ConcreteContinuationAlgebra P,
  ExactConcreteRealization A h⁺
CircularRefinement P h⁺ → False
```

Ainsi, `h⁺` n'est hors ni de l'espace de construction ni de celui des
réalisations concrètes. Il est hors du régime opérationnel tout en conservant
les témoins structurels positifs déjà établis. L'OOD structurel diagnostique
donc un changement de statut; il n'est pas synonyme de mal formé, d'inconnu ou
d'irréalisable.

L'OOD structurel et le désalignement relatif ne sont pas identifiés. La sortie
de régime constitue le diagnostic structurel; le désalignement relatif engage
en outre une norme indépendante et l'adéquation démontrée du régime à cette
norme. Dans l'instance circulaire, le même candidat minimal porte également la
réfutation directe `CircularSpecificationSatisfaction P h⁺ → False`: il
témoigne donc des deux diagnostics.

Les constructions et réfutations sous-jacentes sont vérifiées dans Lean. Le
terme **OOD structurel** et son interprétation constituent actuellement une
proposition conceptuelle, et non encore une définition Lean générique. Voir le
développement complet dans les
[Fondements structurels](docs/fr/fondements_structurels.md).

## Noyau abstrait et interface normative

L'architecture possède deux niveaux de généralité distincts.

Le premier est entièrement polymorphe sur le carrier et ne présuppose ni
histoire, ni périmètre, ni circularité:

- `ExactRegimeClassification` caractérise exactement les carriers d'un régime
  relativement à un carrier canonique;
- `RegimeExit` réunit un candidat, un témoin positif de fidélité et une réfutation
  de son appartenance au régime;
- `UniformRegimeExit` fixe le candidat avant la variation des implémentations et
  demande sa fidélité dans chacune des implémentations fournies.

Le second niveau est paramétrique sur la norme et le régime, mais son carrier est
actuellement spécialisé aux `RootedGeneratedHistory P` pour
`P : CircularPresentation`:

- `NormativeAdequacy` sépare le type des spécifications d'alignement de la famille
  des régimes à évaluer;
- `AdequateAlong` demande l'adéquation normative le long de toutes les occurrences
  effectivement constituées dans une histoire;
- `SpecRelativeHistoryExit` compose sur le même candidat la fidélité, la sortie
  de régime et les témoins d'adéquation à une spécification.

Dans le carrier d'histoires actuel, cette interface permet d'instancier d'autres
normes et d'autres régimes, d'en prouver l'adéquation, puis de produire des
diagnostics de frontière qui préservent l'objet et localisent exactement la
propriété perdue. Le noyau `RegimeExit`, plus abstrait, est directement
réutilisable sur d'autres carriers; étendre toute l'interface normative à un
carrier arbitraire demanderait une généralisation supplémentaire.

## Fondements conceptuels

Le développement respecte quatre distinctions structurantes, organisées selon
un ordre de dépendance:

1. l'individuation est définitionnellement primaire par rapport à l'identité;
2. la totalité est locale et ne se confond pas avec la globalité;
3. la succession est indexée par une localité totale, sans horloge extérieure;
4. le temps et le global sont dérivés de la trajectoire des localités.

```text
présentation
→ localité et rôles
→ occurrences formées et réalisation locale
→ succession
→ histoire
→ antériorité, composition globale et lectures
```

Ces principes structurent l'instance démontrée; ils ne sont pas présentés comme
quatre théorèmes universels indépendants.

### Rôles constitutifs relationnels

Une occurrence est individuée par sa formation et par les relations
structurelles auxquelles elle participe avant d'être projetée vers une lecture,
une étiquette ou une valeur. La méthode préserve ainsi la provenance, la position,
le rôle et la participation à une composition, même lorsque certaines lectures
coïncident.

Cette finesse est conservée dans les interprétations concrètes.
`exactlyInterpretHistory` construit des correspondances inverses entre les
occurrences libres et concrètes, avec accord des sources, des cibles et des pas.
Le changement de représentation n'efface, ne fusionne ni n'ajoute donc une
occurrence sans correspondant dans le cadre de l'interface.

## Architecture du développement

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) établit le théorème
  abstrait des occurrences résiduelles: une continuation positive fidèlement
  segmentée porte exactement une nouvelle occurrence, nécessairement résiduelle;
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) définit la
  classification exacte des régimes, les sorties typées et le théorème abstrait
  de tournant segmenté;
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) construit les
  histoires libres, la réalisation périmétrale, la norme indépendante, le régime
  circulaire, les interprétations concrètes et l'instance complète d'alignement.

## Reproduction et audit

Prérequis: `elan`, ou une installation équivalente capable de lire
`lean-toolchain`.

```bash
lake build
```

Cette commande compile les trois modules dans l'ordre
`SegmentedResidualRole → AbstractSegmentedTurning → StrongPerimetralTurning` et
exécute leurs blocs finaux `#print axioms`.

Depuis la racine du dépôt, vérifier l'intégrité des neuf fichiers scientifiques
du paquet courant sous Linux ou macOS:

```bash
bash scripts/verify-manifest.sh
```

Sous Windows PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

## Documentation détaillée

- [Fondements structurels — français](docs/fr/fondements_structurels.md)
- [Structural foundations — English](docs/en/structural_foundations.md)
- [Méthode des rôles constitutifs relationnels — français](docs/fr/methode_roles_constitutifs_relationnels.md)
- [Method of relational constitutive roles — English](docs/en/relational_constitutive_roles_method.md)
- [Preuve formelle d'alignement relatif — français](docs/fr/preuve_formelle_alignement_relatif.md)
- [Formal proof of relative alignment — English](docs/en/formal_relative_alignment_proof.md)
- [Journal de compilation et d'audit](audit/AUDIT_BUILD.txt)
- [Déclaration d'écriture et de génération par IA](AI_AUTHORSHIP.md)

## Provenance et portée

Le journal `audit/AUDIT_BUILD.txt` déclare que les versions initiales de cinq fichiers
scientifiques ont été copiées depuis le commit source
`31ba1516aaefc5e2ef29aff902fed6af2cd43176` du dépôt
`git@github.com:JohnDoe-collab-stack/meta.git`. Depuis cette importation, les
deux documents français d'origine ont fait l'objet d'une stabilisation
documentaire locale et leurs traductions anglaises ont été ajoutées; un document
méthodologique bilingue a été ajouté localement. Aucun module Lean n'a été
modifié. Les neuf contenus scientifiques actuels correspondent aux empreintes
enregistrées dans `MANIFEST.sha256`.

Le commit source n'est pas accessible publiquement à l'adresse indiquée et la
copie de travail locale ne contient pas son historique Git. Le manifeste permet
donc de contrôler l'intégrité du paquet actuel, mais pas d'établir seul sa
provenance distante. Pour un audit externe reproductible, ces sources devront
être publiées dans le dépôt référencé par `CITATION.cff` avec un commit ou un tag
résolvable.

Le résultat est une première instance complète d'un noyau formel d'alignement
relatif. Il établit l'adéquation dans le cadre défini par `CircularPresentation`;
il ne prétend pas, à lui seul, formaliser toutes les normes ni tous les systèmes
possibles. La preuve est constructive et son audit ne doit dépendre d'aucun
axiome, de `Classical`, de `propext` ou de `Quot.sound`.

## Licence et citation

Le code et la documentation sont distribués sous licence Apache-2.0. Les
métadonnées de citation sont fournies dans `CITATION.cff`.
