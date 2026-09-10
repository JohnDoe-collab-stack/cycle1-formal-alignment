# Expérience finie de transformer constitutif

[English](README.md) | **Français**

Ce dossier contient le premier prototype numérique correspondant à la Gate K.
Le protocole maintient séparés le producteur neuronal, le runtime constitutif
exact, l’effecteur gouverné, le journal primaire immuable et l’auditeur différé.

Le protocole canonique unique est `protocol_v1.json` ; `protocol_v1.py` en est
l’unique implémentation exécutable. Son ensemble d’entraînement, sa sonde de
smoke test et sa sonde confirmatoire préengagée sont séparés, puis leur
disjonction par identifiants et par vues autorisées est vérifiée avant
l’entraînement. Les parcours parent et appris consomment exactement la même
sonde sélectionnée pour leur mode. Un smoke test n’exécute jamais la sonde
confirmatoire.

Installer la dépendance épinglée dans un environnement Python isolé :

```text
python -m pip install -r experiment/requirements-v1.txt
```

Exécuter un smoke test non confirmatoire :

```text
python experiment/protocol_v1.py --mode smoke --config experiment/protocol_v1.json
```

Après le gel du script et de la configuration par un commit source, exécuter
une seule fois le protocole confirmatoire :

```text
python experiment/protocol_v1.py --mode confirmatory --config experiment/protocol_v1.json --output experiment/results/confirmatory_v1.json
```

Le programme refuse d’écraser un résultat existant. Chaque résultat enregistre
les empreintes du script, de la configuration, des données complètes, de
l’ensemble d’entraînement et de la politique de sonde ; toutes les traces
primaires sont scellées avant l’audit différé.

Le protocole a été gelé dans le commit `a4b9a44` avant l’exécution de la sonde
confirmatoire. Son résultat immuable et son rapport bilingue sont disponibles
dans [`results/confirmatory_v1.json`](results/confirmatory_v1.json) et
[`RESULTATS_v1.md`](RESULTATS_v1.md).

Vérifier les artefacts figés sans réexécuter l’entraînement ni les modifier :

```text
python experiment/verify_refinement_v1.py --script experiment/protocol_v1.py --config experiment/protocol_v1.json --result experiment/results/confirmatory_v1.json
```

Le vérificateur en lecture seule contrôle toutes les empreintes gelées, la sonde
confirmatoire exacte, les 24 traces primaires, la frontière constitutive
discrète, la consommation intercycle, le confinement des effets et huit
mutations négatives. Lean démontre séparément la relation canonique de
raffinement discret ; il ne lit pas le résultat JSON.

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
