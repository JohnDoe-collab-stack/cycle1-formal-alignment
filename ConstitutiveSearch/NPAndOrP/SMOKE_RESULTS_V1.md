# Smoke V1 — observation non confirmatoire

Date : 20 septembre 2026. Branche : `research/np-and-or-p-integrated`.
Base Git : `e67d462834b22ab7b5c0a7a32cc55e3c02192e23`, avec les modifications
de travail identifiées par les empreintes ci-dessous. Aucun commit créé.

Ce contrôle exécute quatre exemples. Il ne prouve aucune généralisation ni
la conformité intégrale au plan. Il n'est pas un audit indépendant.

## Protocole figé et reproduction

Commandes, dans la racine du dépôt :

```powershell
lake build
./ConstitutiveSearch/NPAndOrP/SmokeV1.ps1
```

Le build précède le run pour que les modules importés correspondent aux sources.
Entrées : `[0,1,2,4]`. Aucune graine, aucune donnée extérieure.

Empreintes SHA-256 annoncées avant l'exécution :

```text
script_sha256=50770938e2ac59e7cf3c16092db75da1612f0ea3de6bec0529106b45ba476cb4
sources_sha256=8fdd70156e488d10d146db67acf2cb874963b6e49600e27fbca9e00fdf5768af
smoke_sha256=0c689b5c2b1ed5db952159219072bfb8bd4b7ff9674b19a14d4e6ffefd9e57c9
```

L'empreinte `sources_sha256` est celle de la liste ordonnée ordinalement des
empreintes des sources Lean et des trois fichiers de configuration indiqués
dans `SmokeV1.ps1`. Le protocole précise l'encodage et les séparateurs utilisés.
Ce résultat ne doit pas être écrasé après une modification du protocole.

## Sortie observée

Colonnes : entrée, décision, étapes ajoutées, tentatives, travail mesuré des
comparateurs, bit de l'expérience positive, bit de l'expérience négative.
Le travail des comparateurs n'est pas le coût total.

```text
[(0, true, 1, 10, 1089, some true, none),
 (1, false, 2, 26, 3887, some true, none),
 (2, true, 3, 48, 9454, some true, none),
 (4, true, 5, 110, 34335, some true, none)]
```

## Contrôles techniques du même état de sources

- `lake build` : 182 jobs, succès, aucune dépendance axiomatique signalée.
- `lake build ConstitutiveSearch.NPAndOrP.Regression` : 86 jobs, succès,
  aucune dépendance axiomatique signalée.
- `scripts/verify-axiom-audits.ps1` : succès ; `AuditRegression` : 297 jobs.
- Scan de toutes les sources Lean : aucune occurrence de `noncomputable`.

La bibliothèque historique `AuditRegression` et les régressions du nouveau
dossier sont deux contrôles distincts ; leurs nombres de jobs ne sont pas
présentés comme des nombres de théorèmes ou d'attaques indépendantes.
