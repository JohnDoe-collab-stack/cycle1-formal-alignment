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
| §3 : même entrée, organisations positives | `compatibleParent`, `incompatibleParent`, `organizations_constitutively_distinct`, `operational_observation_not_factors_through_input` | Séparateur construit et prouvé. L'expérience reste un champ distinct du run ; son intégration causale et son coût doivent encore être confrontés au contrat complet du plan. |
| §4 : discovery | `runRecordedDiscovery`, `tryMeasuredCandidate`, `exploreRecordedCandidates` | Extraction endogène, exploration effective, préfixe testé et mesures conservés. Les lemmes `*_exact` prouvent l'équivalence avec la recherche de référence. |
| §5.1 : interface générique | `ConstitutiveOperationalInterface`, `produceHistory`, `discoverHistory` | Génération et discovery séparées. `produced_step_does_not_imply_discovery` donne une véritable instance SAT où la génération réussit et la discovery échoue. |
| §5.2–5.3 : instance et parcours | `discoverGeneratedHistoryTransportPath`, son théorème `*_exact` | Le parcours concret traite le résultat optionnel avant de construire l'étape. Le raccord explicite de ce parcours spécialisé au parcours générique doit encore être vérifié au niveau des données. |
| §5.4 : chemins et code | `SequentialHistory.localPath`, `returnedCodes`, `localPath_compiles_to_returnedCodes`, `localPath_length`, `returnedCodes_size` | Séquence hétérogène de chemins primitifs locaux et de codes réellement retournés. Pas de fausse composition entre endpoints frères ; le raccord des affectations est prouvé séparément. |
| §5.5 : préservations | `constitutedOccurrence_order_preserved`, lois de provenance et de différence fraîche, acceptation dans chaque run, `SequentialHistory.readout_preserved` | L'ordre n'est plus confondu avec la simple persistance. La préservation des lectures terminales a sa propre preuve ; elle ne découle pas automatiquement de l'exactitude d'un transport. |
| §6 : succession | `sourceAssignmentExact`, `nextAssignmentExact`, `SequentialHistory`, `terminalAssignment_is_operational_fold` | La sortie appliquée devient l'entrée suivante. Le terminal relit l'affectation finale ; les bits historiques servent à prouver la préservation, pas à remplir indépendamment le terminal. |
| §7.1 : production | `CanonicalStageGeneration`, `initializeConstitutiveHistory`, `produceMeasuredConstitutiveHistory` | Les appels, étapes, unités de provenance et certificats sont émis par les producteurs ; `SequentialStageRun.stats` les projette directement depuis le témoin produit. |
| §7.2 : comparaisons et enfants | `MeasuredComparison`, `MeasuredTransformation`, `MeasuredStateConstruction`, `MeasuredDiscovery` | Résultat et travail issus de la même récursion, y compris les labels unaires et les arrêts précoces. Les enfants construits pendant la discovery sont consommés par le comparateur ; leur construction a un sous-compteur séparé. |
| §7.3–7.5 : total et non-double-comptage | `applyMeasuredTransportCode`, `MeasuredPhase`, `phaseWork`, `Section7AccountingCoverage`, `CanonicalMeasuredAccounting`, `instrumentedWork_partition` | Les récursions productrices émettent les visites d'extraction, candidats extraits, tentatives, requêtes de relation, atomes validés, évaluations d'atomes et applications aux continuations. Chaque opération publiée possède un propriétaire unique ; la trace des candidats testés est prouvée égale aux tentatives et n'est pas chargée deux fois. Le paquet final porte le certificat exhaustif du §7 et la borne du total canonique incluant production, matérialisation, recherches, requêtes, applications, terminal et projection. |
| §7.6 : croissance et borne | `resolution_discoveryAttempts_strict_between`, `instrumentedWork_inputPolynomial` | Croissance des tentatives et borne polynomiale du total canonique relativement à l'encodage unaire effectif. |
| §8 : synthèse | `ConstitutiveAndOrResolutionEvidence`, `ConstitutiveAndOrResolutionFamily` | Le paquet final contient `totalWorkBound`, `section7Coverage`, la comptabilité canonique, l'unicité de propriété des phases et la partition incluant la projection, sans marqueur de clôture universelle. |
| §9 : counterprobes | `Regression.lean` | Lois et contre-tests de substitution, application, échec de discovery, compilation locale, lecture terminale et arrêt précoce. Ne remplace pas une attaque indépendante des API ni le rejeu exhaustif des anciens probes. |
| §10 : validation | Builds, audits axiomatiques et smoke séparés | Contrôles techniques nécessaires, insuffisants pour qualifier le plan entièrement réalisé. |
| §11.19–21 : audit indépendant et clôture | Aucun nouveau marqueur final | **Ouvert : aucun audit indépendant de cet état n'a été exécuté.** |

## Prochaines obligations techniques, sans changement de cible

1. Rejouer les contre-tests du plan et les probes pertinents des audits
   antérieurs, puis obtenir l'audit indépendant requis.

La suppression d'une ancienne surqualification n'est pas comptée comme la
réalisation de l'obligation mathématique correspondante.
