# Intégration constitutive `NP AND/OR P`

Ce dossier est une reconstruction isolée. Il importe les fondations déjà
prouvées, mais ne modifie aucun module scientifique préexistant.

**Chantier ouvert : la conformité intégrale au plan n'est pas établie.**
L'audit adversarial indépendant reste notamment à fermer. La réussite des
builds n'est pas un certificat de cette conformité.

## Chaîne construite

```text
entrée
  → histoire constitutive réellement produite
  → GeneratedStep vers le nouvel état
  → lecture opérationnelle du nouvel endpoint
  → extraction instrumentée des candidats
  → discovery endogène après une suite croissante de leurres
  → schedule indexé par la discovery
  → validation du schedule
  → recherche locale du code
  → application du code effectivement retourné
  → affectation de sortie et décision AND ajoutées à l'état transmis
  → provenance ordonnée et lecteur instrumenté conservés
  → réalisation de l'état opérationnel suivant depuis la cible produite
  → inspection de cet état avant extraction et discovery suivantes
  → bits lus sur les sorties transportées réellement produites
  → terminal construit depuis la trace et ces lectures
  → décision lisant uniquement le terminal
```

L'histoire des `GeneratedStep` est d'abord produite comme un objet dépendant,
puis consommée par une seconde récursion. L'histoire publiée par le run est
extraite du résultat optionnel de ce parcours instrumenté : elle n'est pas
recalculée parallèlement depuis l'entrée. Chaque run stocke la preuve
d'acceptation de sa continuation source et de la sortie réellement calculée.

La procédure publique est :

```lean
executeConstitutiveResolution :
  (input : Nat) → ConstitutiveResolutionRun input
```

Elle n'accepte ni variable utile, ni cible, ni relation, ni code, ni terminal,
ni réponse attendue.

## Modules

- `ConstitutiveOperationalStage.lean` raccorde l'histoire circulaire produite,
  sa réalisation exacte et son readout opérationnel.
- `ConstitutiveInterface.lean` sépare formellement génération constitutive,
  réalisation, discovery opérationnelle, relation et action préservant
  l'acceptation.
- `GenericConstitutiveTraversal.lean` parcourt une histoire générique avec
  échec possible. Une instance SAT concrète prouve qu'une étape générée ne
  fournit pas automatiquement une relation opérationnelle.
- `GenericConcreteRefinement.lean` raccorde les données d'exploration et
  l'histoire complète : le parcours générique retourne les discoveries
  effectivement conservées, sur les générateurs fournis à l'exécution.
- `MeasuredGeneration.lean` produit l'initialisation et l'histoire suivante
  en émettant pendant la récursion les compteurs d'appels, d'étapes, d'unités
  de provenance et de certificats. `SequentialResolution.lean` lit ces champs
  sur le témoin de génération, sans reconstruire quatre constantes après coup.
  L'endpoint initial produit alimente effectivement le producteur suivant.
- `MeasuredComparison.lean`, `MeasuredTransformation.lean` et
  `MeasuredDiscovery.lean` retournent les résultats avec les visites de leurs
  récursions. La discovery active utilise ces résultats. Son équivalence à la
  recherche de référence est prouvée sans axiome.
- `MeasuredComparisonBounds.lean` borne les visites des comparaisons et
  transformations de formules par la taille unaire des données effectivement
  parcourues. Ce sont des bornes de sous-programmes, pas encore du run complet.
- `MeasuredDiscoveryBounds.lean` étend ces bornes à l'extraction, à
  l'exploration, à la validation et à la recherche du code, puis aux sommes
  sur l'histoire retenue. Les enveloppes sont des `CostPolynomial` construits.
- `StoredLocalSchedule.lean` conserve les endpoints retournés par discovery
  et les recherches instrumentées de validation et d'exécution.
- `MeasuredAssignment.lean` et `MeasuredAssignmentBounds.lean` instrumentent
  l'interprétation des codes lors des lectures et bornent les lectures terminales.
- `MeasuredRealization.lean` construit les formules consommées, en émettant
  les unités de construction de littéraux et de listes. Ces unités ne mesurent
  pas encore l'arithmétique de fabrication des labels.
- `MeasuredStateConstruction.lean` construit les résiduels et les enfants
  effectivement consommés pendant la discovery, avec les compteurs de cette
  construction ; ils sont exposés séparément dans `measuredConstructionWork`.
- `EndogenousDiscovery.lean` exécute extraction et exploration, avec nombres de
  visites et de tentatives strictement croissants. La même récursion produit
  aussi le travail mesuré des comparateurs. Les anciens champs de surface
  restent explicitement distincts de ce travail réellement instrumenté.
- `IntegratedProjection.lean` utilise les endpoints et l'affectation entrante
  d'une étape conservée par le run principal. Deux organisations produites
  depuis ces données ont la même projection mais des résultats différents
  sous le même moteur. Le résultat positif est relié à l'action principale.
  `OperationalProjection.lean` conserve le séparateur antérieur de référence.
- `SequentialResolution.lean` valide, exécute le code retourné et transmet son
  affectation de sortie à l'étape suivante.
- `ConstitutiveFeedback.lean` enrichit cette transmission en un
  `ThreadedConstitutiveState` calculable : affectation et lecteur réellement
  retournés, génération reçue, décisions AND ordonnées, provenance et invariants.
  `realizeNextOperationalState` construit la constitution opérationnelle suivante
  depuis la cible produite et la continuation exécutée ; la queue de
  `ConstitutiveExecutionHistory` est indexée par cet état complet. Le même moteur
  de prochaine discovery donne des résultats différents après effacement de
  l'histoire, d'où `nextDiscovery_not_factors`.
- `SequentialHistory.lean` itère cette dépendance typée, construit le terminal
  et dérive les statistiques de la trace. La variable observée est extraite
  du dernier schedule conservé, avec son propre compteur de parcours.
- `GeneratedHistoryExecution.lean` produit d'abord l'histoire constitutive,
  puis la fait consommer par un parcours causal qui conserve explicitement
  `none` et la profondeur du premier échec éventuel. Sur la famille concrète,
  un théorème séparé établit que toutes les discoveries réussissent.
- `ConstitutiveResolution.lean` expose le run public, une famille non bornée,
  des instances YES/NO, le paquet de preuves intégré et les mesures disponibles.
- `ExecutedLocalSchedule.lean` relie les chemins primitifs locaux aux codes
  retournés et prouve que l'affectation finale résulte de leurs applications.
  Il ne compose pas artificiellement des endpoints frères incompatibles.
- `Regression.lean` fixe les obligations et contre-tests formels, notamment
  la substitution de source, l'omission de l'application et l'échec réel de
  discovery après génération.
- `Smoke.lean` contient uniquement des observations exécutables non confirmatoires.

## Portée exacte

Le dossier établit une famille concrète non bornée dans laquelle la
constitution, la discovery et l'exécution locale sont effectivement chaînées,
ainsi qu'une perte opérationnelle non factorisable par l'entrée et la projection
syntaxique seules.

La décision du run intégré replie les bits relus sur l'affectation finale
produite par les atomes retournés et appliqués. La préservation des lectures
antérieures est prouvée séparément dans `SequentialHistory.readout_preserved`.

`structuralProfileCost` et sa borne cubique décrivent l'ancien profil de
surface : ils ne constituent pas une borne du coût complet. Les visites
effectivement produites par les comparateurs sont exposées dans
`measuredComparisonWork`, et celles des constructions internes à la discovery
dans `measuredConstructionWork`. Validation et recherche du code ont leurs
compteurs séparés ; `measuredSearchWork` réunit ces quatre sous-programmes.
`constitutiveMeasuredSearch_inputPolynomial` en prouve une borne relativement
à l'encodage unaire effectif, sans utiliser l'ancien profil de surface.
L'initialisation, la production, la réalisation, la production des schedules,
les requêtes primitives, les applications et les lectures disposent de phases
propriétaires distinctes dans `MeasuredAccounting.lean`. Le total canonique est
une projection déterministe du run, inclut l'expérience de projection et possède
une borne polynomiale relativement à l'encodage unaire. Cette comptabilité porte
sur les opérations instrumentées publiées ; elle n'est pas présentée comme une
mesure du temps machine de Lean ni de l'arithmétique primitive des labels.
`applyMeasuredTransportCode` émet pendant sa récursion le nombre d'atomes
évalués et d'applications aux continuations ; ces valeurs, et non `code.size`
ou une constante ajoutée après coup, alimentent les statistiques publiées.
L'accumulation des décisions, la provenance ordonnée et l'inspection de l'état
transmis sont émises par la récursion de feedback et possèdent trois phases
supplémentaires. La réalisation, l'extraction dépendante et la discovery suivante
restent chargées une seule fois par leurs phases historiques.

La borne de surface est formulée relativement à l'encodage unaire exécutable de l'entrée,
dont la longueur est prouvée exacte.

Il ne contient volontairement aucun marqueur de clôture universelle. Une telle
qualification exige encore un audit adversarial indépendant du dossier complet.
À la demande de l'utilisateur, cet audit externe est différé et ne bloque pas
la poursuite de l'implémentation.

## Vérification

Chaque fichier Lean contient un unique bloc `AXIOM_AUDIT`. Le dossier est relié
à la cible par la racine `ConstitutiveSearch.NPAndOrP.Regression` :

```text
lake build ConstitutiveSearch.NPAndOrP.Regression
```

Les validations globales restent :

```text
lake build
lake build AuditRegression
bash scripts/verify-manifest.sh
```

Sous Windows, les contrôles natifs correspondants sont :

```text
powershell -File scripts/verify-axiom-audits.ps1
powershell -File scripts/verify-manifest.ps1
```
