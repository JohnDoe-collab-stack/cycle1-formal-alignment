# Contrôle de conformité du chantier isolé

Document de chantier, pas rapport d'audit indépendant et pas certificat de
clôture. Il devra être retiré de l'arbre destiné à `main` conformément à
`AGENTS.md`. Le plan de référence reste
`NP_AND_OR_P_CONSTITUTIVE_PLAN.md` ; ses obligations ne sont pas réduites par
ce constat.

## État

**La conformité intégrale n'est pas établie.** Les constructions ci-dessous
sont présentes ; les obligations ouvertes sont explicitement séparées. Le
travail porte sur la constitution progressive annoncée par le projet, pas
sur une autre conjecture.

## Vérification par partie du plan

| Partie | Construction vérifiable | État et limite |
| --- | --- | --- |
| §2.1–2.3 : endogénéité et causalité | `generateCanonicalStageFromSource`, `produceThreadedGeneratedHistoryFrom`, `generatedRecordedDiscoveryRun`, `executeSequentialStageFromRecorded` | La cible produite alimente le producteur suivant et la recherche ; le builder consomme les données reçues, pas une reconstruction canonique indépendante. |
| §3 : même entrée, organisations positives et primitives §3.1 | `IntegratedProjectionExperiment`, `runSection31ReferenceProjection`, `runMeasuredProjection_refines_section31`, `Section31PrimitiveRaccord`, `integrated_projection_not_factors` | L'expérience est construite depuis le premier stage réellement exécuté. La sémantique de référence formalise séparément la chaîne imposée au §3.1 — recherche exacte, production du code fini, application du code, lecture de la continuation retournée. Le théorème générique `runMeasuredProjection_refines_section31` prouve que l'implémentation mesurée a exactement les mêmes sorties terminales et le même nombre d'atomes pour toute source et toute cible ; `positiveCodeAtoms` et `negativeCodeAtoms` exposent respectivement les comptes exacts `1` et `0` dans l'expérience, puis `projectionPositiveCodeAtoms` et `projectionNegativeCodeAtoms` dans le paquet final. `projectionUsesSection31Primitives` incorpore aussi le raccord sémantique dans ce paquet. Le remplacement des anciennes primitives instrumentées est donc justifié formellement, et non par équivalence documentaire. |
| §4 : discovery | `runRecordedDiscovery`, `tryMeasuredCandidate`, `exploreRecordedCandidates` | Extraction endogène, exploration effective, préfixe testé et mesures conservés. Les lemmes `*_exact` prouvent l'équivalence avec la recherche de référence. |
| §5.1 : interface générique | `ConstitutiveOperationalInterface`, `produceHistory`, `discoverHistory` | Génération et discovery séparées. `produced_step_does_not_imply_discovery` donne une véritable instance SAT où la génération réussit et la discovery échoue. |
| §5.2–5.3 : instance et parcours | `discoverGeneratedHistoryTransportPath`, son théorème `*_exact` | Le parcours concret traite le résultat optionnel avant de construire l'étape. Le raccord explicite de ce parcours spécialisé au parcours générique doit encore être vérifié au niveau des données. |
| §5.4 : chemins et code | `SequentialHistory.localPath`, `returnedCodes`, `localPath_compiles_to_returnedCodes`, `localPath_length`, `returnedCodes_size` | Séquence hétérogène de chemins primitifs locaux et de codes réellement retournés. Pas de fausse composition entre endpoints frères ; le raccord des affectations est prouvé séparément. |
| §5.5 : préservations | `constitutedOccurrence_order_preserved`, lois de provenance et de différence fraîche, acceptation dans chaque run, `SequentialHistory.readout_preserved` | L'ordre n'est plus confondu avec la simple persistance. La préservation des lectures terminales a sa propre preuve ; elle ne découle pas automatiquement de l'exactitude d'un transport. |
| §6 : succession | `Section6OperationalSuccessionEvidence`, `sourceAssignmentExact`, `nextAssignmentExact`, `FullHistoryExecution`, `GenericRefinedHistory`, `terminalAssignment_is_operational_fold` | Le paquet agrégé exact du §6 est `Section6OperationalSuccessionEvidence`. `sourceIsInitial` raccorde l'exécuteur à l'entrée initiale ; l'index dépendant de `SequentialHistory` et `successionIsTyped` imposent que la sortie de chaque tête indexe la queue ; `discoveryProvenanceIsRetained` et `returnedCodesComeFromDiscoveredPath` relient chaque atome à la discovery exécutée ; `targetIsHistoryEndpoint` identifie la cible terminale à la fin de l'histoire ; `executedAtomsAreGeneratedSteps`, `compositionCandidatesAreZero` et `terminalContinuationIsOperationalFold` donnent exactement les trois égalités quantitatives et terminales demandées. Le terminal est produit par `terminalFromSequentialHistory`, jamais rempli directement avec un endpoint déclaré. |
| §7.1 : production | `CanonicalStageGeneration`, `initializeConstitutiveHistory`, `produceMeasuredConstitutiveHistory` | Les appels, étapes, unités de provenance et certificats sont émis par les producteurs ; `SequentialStageRun.stats` les projette directement depuis le témoin produit. |
| §7.2 : comparaisons et enfants | `MeasuredComparison`, `MeasuredTransformation`, `MeasuredStateConstruction`, `MeasuredDiscovery` | Résultat et travail issus de la même récursion, y compris les labels unaires et les arrêts précoces. Les enfants construits pendant la discovery sont consommés par le comparateur ; leur construction a un sous-compteur séparé. |
| §7.3–7.5 : total et non-double-comptage | `applyMeasuredTransportCode`, `MeasuredPhase`, `phaseWork`, `Section7AccountingCoverage`, `CanonicalMeasuredAccounting`, `ConstitutiveAndOrResolutionPerInputEvidence`, `instrumentedWork_partition` | Les récursions productrices émettent les visites d'extraction, candidats extraits, tentatives, requêtes de relation, atomes validés, évaluations d'atomes et applications aux continuations. Chaque opération publiée possède un propriétaire unique ; la trace des candidats testés est prouvée égale aux tentatives et n'est pas chargée deux fois. Pour chaque entrée, l'évidence finale porte directement `phaseWorkExact`, `totalWorkExact`, `section7Coverage`, `phaseOwnershipUnique` et `accountingPartition` pour son propre `core.run` ; aucun détour par un théorème du paquet familial n'est nécessaire. |
| §7.6 : croissance et borne | `resolution_discoveryAttempts_strict_between`, `instrumentedWork_inputPolynomial` | Croissance des tentatives et borne polynomiale du total canonique relativement à l'encodage unaire effectif. |
| §8 : synthèse | `ConstitutiveAndOrResolutionEvidence`, `ConstitutiveAndOrResolutionPerInputEvidence`, `ConstitutiveAndOrResolutionFamily` | `ConstitutiveAndOrResolutionEvidence` reste le noyau constitutif. `ConstitutiveAndOrResolutionPerInputEvidence` est l'évidence finale par entrée : elle agrège ce noyau et le ledger canonique exact du même run, sa couverture exhaustive, sa propriété unique, sa partition et sa borne polynomiale. La famille publie ces évidences par `perInput`, sans marqueur de clôture universelle. |
| §9 : counterprobes | `Regression.lean` | Lois et contre-tests de substitution, application, échec de discovery, compilation locale, lecture terminale et arrêt précoce. Ne remplace pas une attaque indépendante des API ni le rejeu exhaustif des anciens probes. |
| §10 : validation | Builds, audits axiomatiques et smoke séparés | Contrôles techniques nécessaires, insuffisants pour qualifier le plan entièrement réalisé. |
| §11.19–21 : audit indépendant et clôture | Aucun nouveau marqueur final | **Ouvert : aucun audit indépendant de cet état n'a été exécuté.** |

## Prochaines obligations techniques, sans changement de cible

1. Rejouer les contre-tests du plan et les probes pertinents des audits
   antérieurs, puis obtenir l'audit indépendant requis.

La suppression d'une ancienne surqualification n'est pas comptée comme la
réalisation de l'obligation mathématique correspondante.
