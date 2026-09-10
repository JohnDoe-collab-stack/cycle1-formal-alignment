# Résultat confirmatoire v1

[English](RESULTS_v1.md) | **Français**

## Statut

Le run confirmatoire a été exécuté après le gel du protocole dans le commit
`7aba368`. Il s’est achevé avec le code de sortie 0. Tous les critères
préengagés ont réussi pour les trois graines préengagées.

Résultat de référence :
[`results/confirmatory_v1.json`](results/confirmatory_v1.json)

SHA-256 du résultat de référence :
`397c7bf5b39dd5f08ab565588314a9466538a5aaebb836d43b202ce6925c5648`

## Provenance figée

| Élément | Valeur |
| --- | --- |
| protocole | `constitutive-transformer-v1` |
| graines | `11`, `29`, `47` |
| SHA-256 du script | `e9fa57cf9859d3373adb63a466aa37aad99ee3f85ca5fd492e5244f364253493` |
| SHA-256 de la configuration | `149ab76af8db75f9ee79af24188ecefa7aad434bb26ecc735f414df7921d96f9` |
| SHA-256 des données | `5a46f24b76e81eead471980e85733d3ec8eaa40312446f4a98334a0dd2caeb94` |
| Python | `3.12.14` |
| NumPy | `2.3.5` |
| plateforme | `Windows-11-10.0.26200-SP0` |

## Faits

Chaque graine a produit huit traces primaires complètes : parent, premier cycle
appris, second cycle appris, ablation intercycle, contrôle à relation active,
deux contrôles inertes et renommage cohérent des adresses. L’auditeur n’a été
exécuté qu’après scellement du journal, dont le SHA-256 est resté identique après
l’audit.

| Graine | Probabilité parent | Cycle appris 1 | Cycle appris 2 | Cycle 2 ablaté | Tous les contrôles |
| ---: | ---: | ---: | ---: | ---: | :---: |
| 11 | 0,1762 | 0,7316 | 0,2714 | 0,7316 | oui |
| 29 | 0,1751 | 0,7311 | 0,2709 | 0,7311 | oui |
| 47 | 0,1853 | 0,7355 | 0,2754 | 0,7355 | oui |

Pour chaque graine, les faits observés comprennent :

- l’absence de la cible dans la vue neuronale autorisée ;
- la modification du paramètre prédictif, de la prédiction et de la proposition
  par l’apprentissage ;
- l’identité exacte entre prédiction produite et valeur consommée par la
  proposition ;
- la conservation de la proposition parent, rejetée en position 0 pour le motif
  fixé de sortie du régime et de la norme ;
- l’admission, la satisfaction normative, la certification et l’effectuation de
  la première proposition apprise ;
- l’identité de cette proposition avec la relation consommée par le second
  cycle ;
- la réutilisation des mêmes paramètres appris au second cycle ;
- la modification de la seconde prédiction et de la seconde proposition lorsque
  la seule incorporation intercycle est omise ;
- l’effet de la relation active et l’inertie du contrôle correspondant ;
- l’invariance de la prédiction sous renommage technique cohérent ;
- l’exactitude de la mémoire pour les deux requêtes d’attention déclarées ;
- l’impossibilité persistante de l’effet gouverné rejeté ;
- l’accord du régime et de la norme implémentée indépendamment sur le domaine
  fini ;
- l’absence de modification des traces primaires par l’audit différé.

## Interprétation

Dans cette tâche finie et figée, la prédiction apprise modifie causalement la
proposition constitutive ; la proposition est consommée par le cycle suivant ;
et un candidat normativement rejeté reste auditable tandis que son effet externe
gouverné est confiné. L’expérience numérique réalise les mêmes séparations que
l’architecture Lean sans transformer la sortie neuronale en identité, norme ou
admission.

## Limites

Ce résultat n’établit ni l’alignement général des transformers, ni l’autonomie
sur un horizon non borné, ni la réduction des hallucinations en langue
naturelle, ni le passage à l’échelle des modèles entraînés en production. Il
s’agit d’une observation confirmatoire finie, non d’un théorème Lean ni d’une
revendication de benchmark.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche du projet. Ce rapport a été écrit de A à Z par des
> modèles de la série ChatGPT d’OpenAI, sous direction humaine et au cours
> d’interactions successives. Voir la
> [déclaration bilingue complète](../AI_AUTHORSHIP.md).
