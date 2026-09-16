# Règles de travail du dépôt

Ces règles s’appliquent à tout travail réalisé dans ce dépôt. Elles protègent
la constructivité des preuves, l’autonomie du résultat et la reproductibilité
des expériences.

## Lean

Pour tout fichier `.lean` créé ou modifié :

- conserver une preuve strictement constructive ;
- ne jamais introduire `axiom`, `sorry` ou trou de preuve ;
- ne jamais introduire ni conserver de déclaration marquée `noncomputable` ;
- ne dépendre ni de `Classical`, ni de `propext`, ni de `Quot.sound` ;
- construire positivement les témoins utilisés ;
- rendre exécutables les définitions qui produisent des données dans `Type`,
  notamment en remplaçant les récursions non compilables par des récursions
  structurelles acceptées par le générateur de code ;
- ne pas masquer une construction non calculable derrière une projection
  propositionnelle lorsque la couche témoin est constitutive du résultat ;
- ne pas remplacer une obligation concrète par une hypothèse externe laissée
  ouverte ;
- ne pas confondre un contrat abstrait conditionnel avec une instance construite.

Un théorème conditionnel est admis lorsqu’il définit honnêtement une interface
générique. Lorsqu’une gate exige une réalisation concrète, ses hypothèses
doivent être fermées par une construction présente dans le dépôt.

### Audit axiomatique et calculabilité

Chaque fichier Lean doit contenir exactement un bloc placé à sa toute fin :

```lean
/- AXIOM_AUDIT_BEGIN -/
#print axioms DeclarationPrincipale
/- AXIOM_AUDIT_END -/
```

- Mettre à jour le bloc existant au lieu d’en ajouter un second.
- Utiliser les noms complets des déclarations principales ajoutées ou modifiées.
- Ne laisser aucun placeholder dans une commande `#print axioms`.
- Vérifier que chaque nom existe et que chaque audit n’affiche aucun axiome.
- Ne pas livrer un fichier dont l’audit mentionne une dépendance interdite.
- Scanner tous les fichiers Lean et exiger l’absence totale du mot-clé
  `noncomputable` avant toute livraison.

## Séparations conceptuelles

Les distinctions suivantes doivent rester visibles dans les types et dans la
documentation :

```text
construction          ≠ réalisation
réalisation           ≠ admission
admission             ≠ satisfaction normative
norme                 ≠ adéquation du régime
proposition           ≠ incorporation
apprentissage         ≠ succession constitutive
sortie opérationnelle ≠ sortie représentationnelle
OOD structurel        ≠ frontière diagonale de représentation
diagnostic            ≠ prévention de l’effectuation
```

## Réemploi et transplantation

Un matériau de travail antérieur peut informer la reconstruction, mais ne doit
pas devenir une dépendance scientifique ou technique du dépôt.

- Conserver les fragments bruts et leur analyse hors du dépôt.
- N’intégrer que des éléments autonomes, renommés dans le vocabulaire local et
  raccordés aux interfaces locales.
- Remplacer toute dépendance extérieure par une définition locale nécessaire ou
  par un import déjà présent dans le dépôt.
- Vérifier les droits de réemploi ; exclure tout contenu tiers de statut incertain.
- Soumettre chaque transplantation aux mêmes exigences de preuve, de test et
  d’audit que du code nouvellement écrit.
- Ne conserver aucun chemin, nom de projet, commentaire ou historique extérieur
  dans les fichiers publiés.

## Expériences et reproductibilité

Pour toute exécution utilisée dans une revendication scientifique :

- figer le script exécuté avant le run confirmatoire ;
- enregistrer son empreinte, la commande complète, les paramètres, les graines
  et les données ou leur empreinte ;
- associer sans ambiguïté les sorties au script qui les a produites ;
- ne jamais modifier silencieusement un protocole après observation des résultats ;
- créer une nouvelle version lorsqu’un script scientifique déjà cité doit évoluer ;
- isoler les smoke tests et les identifier explicitement comme non confirmatoires ;
- ne jamais écraser un résultat de référence.

Un résultat expérimental reste une observation. Il ne devient pas un théorème
Lean par sa seule reproductibilité.

## Git et documents temporaires

- Ne pas créer de commit, pousser, fusionner ou modifier l’historique sans
  demande explicite de l’utilisateur.
- Préserver les modifications utilisateur sans rapport avec la tâche.
- Ne jamais ajouter à l’index Git les fragments bruts ou espaces d’extraction.
- Les plans d’implémentation, registres de décision, journaux de migration et
  autres documents de chantier temporaires peuvent exister sur une branche de
  travail.
- Tous ces documents temporaires doivent être supprimés dans la merge request
  ou pull request qui intègre le chantier dans `main`.
- Si un document temporaire a été commité sur la branche, sa suppression doit
  faire partie de la même merge request ; l’arbre résultant de `main` ne doit
  pas le contenir.
- Cette règle ne concerne pas les README, les documents scientifiques
  canoniques, les instructions de reproduction ni les rapports finaux déclarés
  comme livrables.
- L’ouverture d’une merge request ne clôt pas le chantier. Celui-ci n’est
  achevé qu’après fusion validée dans `main` et vérification de l’état fusionné.
- La fusion effective reste soumise à une demande explicite de l’utilisateur,
  même lorsque la merge request est techniquement prête.

Avant la merge request vers `main`, vérifier :

- l’absence de documents temporaires et de fragments bruts dans l’arbre final ;
- la réussite de `lake build` et de tous les audits axiomatiques ;
- l’absence totale de déclaration `noncomputable` dans les sources Lean ;
- la validité des liens documentaires locaux ;
- la cohérence des versions française et anglaise ;
- le recalcul du manifeste depuis l’état final ;
- la propreté du diff et l’absence de fichiers générés ou de caches.

Après la fusion dans `main`, vérifier sur le commit fusionné :

- que les documents temporaires sont absents de l’arbre ;
- que le manifeste correspond exactement aux fichiers publiés ;
- que `lake build` réussit encore ;
- que la tête de `main` contient bien l’ensemble des commits attendus.
