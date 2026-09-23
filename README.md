# c3_experimental — laboratoire exploratoire (branche C3 de Conway 99)

## Pour la relecture

**Énoncé.** Un graphe fortement régulier de paramètres (99, 14, 1, 2) n'a aucun automorphisme d'ordre 3.

**Statut.** Preuve candidate, pas encore relue par un tiers. Elle est entièrement vérifiée en Lean 4 / Mathlib, à partir de la
définition de Mathlib d'un graphe fortement régulier, sans `sorry` ni axiome supplémentaire, et sans entrée extérieure.

**Par où commencer.**
1. `pdf/preuve_c3.pdf` : la preuve mathématique (6 pages, en français).
2. `c3formal/README.md` : la formalisation Lean. L'énoncé final est `C3.no_order3` (`c3formal/C3formal/FixLemma.lean`) :
   tout automorphisme σ tel que σ³ = 1 est l'identité. Un relecteur n'a à contrôler que cet énoncé ; tout le reste est
   vérifié par le noyau de Lean.
3. `ENVIRONNEMENT.md` : versions exactes, reproduction de la vérification, contrôle d'intégrité (`SHA256SUMS`).
4. `JOURNAL.md`, `IDEES.md`, `notes/` : le déroulé de la recherche, y compris les pistes abandonnées ; `scripts/`, `logs/`,
   `data/` : les calculs exploratoires et leurs sorties.

Ce dossier est l'état exact du laboratoire sur la machine d'origine. Seuls l'environnement Python (`.venv/`) et le cache
Lean/Mathlib (`c3formal/.lake/`) sont exclus, parce qu'ils sont régénérables à l'identique (voir `ENVIRONNEMENT.md`).
`data/` contient des copies de documents tiers (texte de l'article d'Ishida, tables de Brouwer) : à retirer avant toute
publication du dépôt.

---

Session ouverte le 2026-09-23 à la demande de l'utilisateur : régime de recherche **exploratoire**.

## Règles d'isolation
- Tout ce qui est produit ici reste ici (scripts, notes, calculs, journaux, résultats négatifs).
- `Desktop/c3_recherche_annexe` (dépôt `conway99-c3`) : **lecture seule**. Aucun fichier modifié, aucun git.
- `conway99-involution` : **non consulté**.
- Rien de ce laboratoire n'entre dans la mémoire ni dans les notes persistantes du travail principal.
- Environnement Python isolé : `.venv/` (numpy, sympy, networkx, python-sat).

## Étiquettes de statut (celles de la consigne, dans toutes les notes)
- **ÉTABLI** : démontré ou déjà certifié dans C3 (dépôt conway99-c3) ou dans la littérature lue.
- **DÉRIVÉ** : conséquence démontrée ici (preuve écrite dans `notes/`) ; reste à faire relire par un humain.
- **OBSERVÉ** : constat expérimental exact sur des cas précis (toujours dire lesquels, log à l'appui).
- **CONJECTURE** : énoncé précis, falsifiable, non démontré.
- **HEURISTIQUE** : intuition ou analogie qui guide.
- **SPÉCULATION** : idée volontairement risquée.
- **RÉFUTÉ** : testé et faux (avec la raison et ce que l'échec enseigne).

Une affirmation « tue la branche C3 » n'est jamais présentée comme acquise tant qu'elle n'est pas DÉRIVÉ **et**
testée sur des graphes réels où elle doit ne rien tuer — et même alors, elle attend une relecture humaine.

## Fichiers
- `JOURNAL.md` : journal horodaté.
- `IDEES.md` : registre des pistes (statut, potentiel, test, verdict).
- `notes/` : développements mathématiques.
- `scripts/` : code ; `logs/` : sorties ; `data/` : données extraites (copies) du dépôt.
