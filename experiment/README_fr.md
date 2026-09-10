# Expérience finie de transformer constitutif

[English](README.md) | **Français**

Ce dossier contient le premier prototype numérique correspondant à la Gate K.
Le protocole maintient séparés le producteur neuronal, le runtime constitutif
exact, l’effecteur gouverné, le journal primaire immuable et l’auditeur différé.

Le protocole figé est `protocol_v1.json` ; `protocol_v1.py` en est l’unique
implémentation exécutable. Le résultat de référence ne doit jamais être écrasé.

Installer la dépendance épinglée dans un environnement Python isolé :

```text
python -m pip install -r experiment/requirements-v1.txt
```

Exécuter un smoke test non confirmatoire :

```text
python experiment/protocol_v1.py --mode smoke --config experiment/protocol_v1.json
```

Exécuter une fois le protocole confirmatoire figé vers un nouveau chemin :

```text
python experiment/protocol_v1.py --mode confirmatory --config experiment/protocol_v1.json --output experiment/results/confirmatory_v1.json
```

Le programme refuse d’écraser un résultat existant. Chaque résultat enregistre
les empreintes du script, de la configuration et des données ; toutes les
traces primaires sont scellées avant l’audit différé. Le rapport sépare faits,
interprétation et limites.

Le run de référence immuable et son rapport lisible sont disponibles dans
[`results/confirmatory_v1.json`](results/confirmatory_v1.json) et
[`RESULTATS_v1.md`](RESULTATS_v1.md).

Cette expérience finie ne prouve ni l’alignement général des transformers, ni
l’autonomie sur un horizon non borné, ni l’entraînement à l’échelle de la
production, ni la réduction des hallucinations en langue naturelle.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche du projet. Ce document et l’implémentation
> expérimentale ont été écrits de A à Z par des modèles de la série ChatGPT
> d’OpenAI, sous direction humaine et au cours d’interactions successives. Voir
> la [déclaration bilingue complète](../AI_AUTHORSHIP.md).
