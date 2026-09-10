# Expérience d’auto-extension de programmes typés

[English](README.md)

Ce dossier contient le témoin exécutable séparé de la Gate N. Il ne modifie ni
ne versionne l’expérience gelée `experiment/protocol_v1.*`.

Le protocole emploie une unique règle de frontière sans rang sur un corpus typé
fini. Une première composition certifiée est incorporée au corpus successeur
effectif ; la même règle est ensuite réappliquée à ce corpus produit. Le journal
consigne les requêtes exactes au worker sans état, les capacités acquises, les
sondes générées, le ledger cumulatif des expositions, l’incorporation exacte et
les contrefactuels d’incorporation et d’apprentissage.

Le worker ne reçoit ni sonde ni cible future pendant l’apprentissage. La mesure
reçoit l’entrée de sonde, mais aucune cible, et ne peut mettre l’état à jour. Le
comportement attendu est calculé indépendamment par la sémantique totale des
programmes.

Smoke test de développement :

```powershell
py run.py --mode smoke --output "$env:TEMP\typed-program-smoke.json"
py verify.py "$env:TEMP\typed-program-smoke.json" --self-test
```

Le run confirmatoire est volontairement bloqué tant que l’arbre de travail est
sale. Après gel des sources scientifiques et du protocole par commit, il devra
écrire dans un chemin neuf de `results/` ; aucune sortie existante n’est
écrasée.

Ce témoin fini n’établit ni la synthèse générale de programmes, ni une autonomie
non bornée, ni l’alignement général des transformers.
