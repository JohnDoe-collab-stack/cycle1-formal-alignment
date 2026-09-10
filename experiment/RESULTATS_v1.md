# Résultat confirmatoire v1

[English](RESULTS_v1.md) | **Français**

## Statut

Le protocole canonique a été gelé dans le commit `a4b9a44` avant l’exécution de
la sonde confirmatoire. L’unique run confirmatoire s’est achevé avec le code de
sortie 0 ; tous les critères préengagés ont réussi pour les graines `11`, `29`
et `47`.

Résultat de référence :
[`results/confirmatory_v1.json`](results/confirmatory_v1.json)

SHA-256 du résultat de référence :
`e483c0e0a046e2f81b03b043be956ad575f972e9ffb1b756c53eda3b9896928c`

## Provenance figée

| Élément | Valeur |
| --- | --- |
| protocole | `constitutive-transformer-v1` |
| commit de gel des sources | `a4b9a44` |
| graines | `11`, `29`, `47` |
| sonde sélectionnée | `confirmatory-0`, ordinal `1` |
| SHA-256 du script | `ab27a54ae7cf62a5c5f9dbb4d6ef3f6db6eb214db606498884d976df780eb04d` |
| SHA-256 de la configuration | `008993ba6a21e5e9731869e1dbf4f16edc1ffa29c380486e738e9b26516241c0` |
| SHA-256 des données complètes | `3ae9c050758295f2f56bd3e216d48241f51b3ee48544b50eb4f18b1c9f003f08` |
| SHA-256 de l’ensemble d’entraînement | `4a2a43bd7888355d26c888f795c6719bd7d5553e1c15ab4372ff19d7bc8f8ae0` |
| SHA-256 de la politique de sonde | `28822c4762958997f8da6c5d18121b896f6fac650e1030e39b23ea7d4343fd57` |
| SHA-256 de la vue d’entraînement | `b9522be46ba717683c4064596ad7e8c0311a2c0ef8ebe0903f2c8442d5c6e9d2` |
| SHA-256 de la vue confirmatoire | `2eecfe1b1f90c346511a19a3c52ac4a46c9d4d3cd12103c43e5e3ac00220233b` |
| Python | `3.12.14` |
| NumPy | `2.3.5` |
| plateforme | `Windows-11-10.0.26200-SP0` |

Le cas d’entraînement, la sonde de smoke test et la sonde confirmatoire ont des
identifiants et des vues autorisées distincts. Le smoke test a sélectionné
l’ordinal `0` ; le run confirmatoire a sélectionné l’ordinal `1`. Chaque trace
confirmatoire enregistre le rôle `confirmatory`, l’identifiant
`confirmatory-0` et l’ordinal `1`.

## Faits

Chaque graine a produit huit traces primaires : parent, premier cycle appris,
second cycle appris, ablation intercycle, contrôle à relation active, deux
contrôles inertes et renommage cohérent des adresses. Le journal a été scellé
avant l’audit différé.

| Graine | Probabilité parent | Cycle appris 1 | Cycle appris 2 | Cycle 2 ablaté | Tous les contrôles |
| ---: | ---: | ---: | ---: | ---: | :---: |
| 11 | 0,1761 | 0,7314 | 0,2713 | 0,7314 | oui |
| 29 | 0,1750 | 0,7309 | 0,2708 | 0,7309 | oui |
| 47 | 0,1852 | 0,7354 | 0,2753 | 0,7354 | oui |

Pour chaque graine :

- les ensembles d’entraînement et de sondes sont exactement liés et disjoints ;
- les parcours parent et appris consomment la même sonde confirmatoire ;
- l’apprentissage modifie le paramètre prédictif, la prédiction et la proposition ;
- la prédiction produite et la valeur constitutivement consommée sont identiques ;
- la proposition parent est conservée et rejetée en position 0 pour le motif
  fixé de sortie du régime et de la norme ;
- la première proposition apprise est admise, normative, certifiée et effectuée ;
- cette proposition est exactement la relation consommée au second cycle ;
- le second cycle réutilise les mêmes paramètres appris ;
- l’omission de la seule incorporation intercycle modifie la seconde proposition ;
- la relation active modifie la prédiction, contrairement au contrôle inerte ;
- le renommage cohérent des adresses conserve la prédiction ;
- la mémoire d’attention est exacte pour les deux requêtes déclarées ;
- l’effet gouverné rejeté reste confiné ;
- le régime et la norme implémentée indépendamment concordent sur le domaine fini ;
- l’audit différé laisse inchangé le journal primaire scellé.

## Vérification en lecture seule

```text
python experiment/verify_refinement_v1.py --script experiment/protocol_v1.py --config experiment/protocol_v1.json --result experiment/results/confirmatory_v1.json
```

Le vérificateur a accepté 3/3 runs et 24/24 traces primaires, retrouvé toutes
les empreintes gelées et rejeté huit mutations : réécriture du candidat, effet
non certifié, lien intercycle absent, prédiction substituée, rôle ou identité de
sonde substitué, champ primaire manquant et provenance substituée. Il ne
réexécute pas l’entraînement et ne modifie aucun artefact.

## Interprétation

Dans cette tâche finie et figée, un paramètre appris uniquement depuis
l’ensemble d’entraînement modifie la proposition sur la sonde confirmatoire
distincte et préengagée. Cette proposition est consommée par le cycle suivant,
et un candidat normativement rejeté reste auditable tandis que son effet externe
gouverné est confiné.

## Limites

Il s’agit d’une observation numérique finie. Ce n’est ni un théorème Lean, ni
un résultat général d’alignement des transformers, ni un résultat sur un
horizon non borné, ni un benchmark d’hallucinations en langue naturelle, ni une
revendication d’entraînement à l’échelle de la production.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche. Ce rapport a été écrit de A à Z par des modèles de
> la série ChatGPT d’OpenAI, sous direction humaine et au cours d’interactions
> successives. Voir la
> [déclaration bilingue complète](../AI_AUTHORSHIP.md).
