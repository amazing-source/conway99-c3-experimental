# Environnement et intégrité

## Machine d'origine
Windows 11 Famille 10.0.26200, Git Bash. Tout le travail a été fait dans ce dossier (`Desktop/c3_experimental`).

## Outils (versions exactes)
| outil | version | où |
|---|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc2` | `c3formal/lean-toolchain` |
| Mathlib et dépendances | commits exacts | `c3formal/lake-manifest.json` (Mathlib `v4.35.0-rc2`) |
| elan | 4.2.4 (227caca13 2026-08-25) | `tools/elan.zip`, `tools/elan_pkg/` |
| Tectonic (LaTeX) | 0.17.0 | `tools/tectonic.zip`, `tools/tectonic_pkg/` |
| Python | 3.14.3 | paquets : `requirements.txt` |

## Ce qui n'est pas dans le dépôt (régénérable à l'identique)
| dossier local | contenu | pour le recréer |
|---|---|---|
| `.venv/` (233 Mo) | environnement Python : uniquement les paquets pip de `requirements.txt` | `python -m venv .venv` puis `.venv/Scripts/pip install -r requirements.txt` |
| `c3formal/.lake/` (plusieurs Go) | clones de Mathlib et de ses dépendances, cache compilé, compilation de `C3formal` | `cd c3formal && lake exe cache get && lake build` |

Rien d'autre n'a été exclu : scripts, journaux, notes, données, sorties (`logs/`), PDF et sources LaTeX, sources Lean, outils
téléchargés (`tools/`), y compris les résultats négatifs. Le dépôt git vide que `lake new` avait créé dans `c3formal/` (aucun
commit, aucun objet) a été retiré pour que `c3formal/` soit suivi normalement.

## Vérifier l'intégrité (octet par octet)
`.gitattributes` désactive toute conversion de fin de ligne : les fichiers sont restitués exactement tels qu'ils étaient.
`SHA256SUMS` contient l'empreinte SHA-256 de chaque fichier suivi (sauf lui-même). Après clonage :

```
sha256sum -c SHA256SUMS
```

## Reproduire la vérification Lean
```
cd c3formal
lake exe cache get
lake build                          # ~2240 tâches
lake env lean C3formal/Check.lean   # axiomes : [propext, Classical.choice, Quot.sound]
lake build Challenge Solution
lake comparator --paranoid          # Linux ; attendu : « Your solution is okay! »
```
Sorties de référence sur la machine d'origine : `logs/lean_axioms_final.log`, `logs/comparateur_local_2026-09-23.log`.
`lake comparator` isole la compilation et l'export dans un bac à sable `bwrap`, qui n'existe que sous Linux ; sous Windows il
faut `--inadvisably-no-sandbox`, et Lake prévient alors que le verdict n'est pas fiable. La vérification complète, avec bac à
sable, tourne sur GitHub Actions à chaque modification de `c3formal/` (`.github/workflows/lean-verify.yml`).

Mémoire, pour qui relance sur une petite machine : un processus `lean` qui importe le projet occupe quelques centaines de Mo de
RAM réelle, mais engage environ 3 Go (fichiers `.olean` de Mathlib chargés en mémoire). `con-leche` engage environ 5 Go pour
moins de 1 Go de RAM réelle. Un plafond sur la mémoire engagée (et non sur la RAM) le fait donc échouer sans raison. Avec
`--paranoid`, il lance un travailleur par fil du processeur ; seul, on peut le limiter : `con-leche --jobs=2 export.ndjson`.
Enfin, `lake env leanchecker C3formal` rejoue les 22 modules en parallèle, chacun avec sa propre copie de Mathlib : environ
8 Go de RAM ; il faut vérifier les modules un par un, ou passer par `lake comparator`.

## Recompiler le PDF
```
cd pdf
../tools/tectonic_pkg/tectonic.exe -X compile preuve_c3.tex
```
