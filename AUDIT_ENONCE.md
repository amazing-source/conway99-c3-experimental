# Audit de l'énoncé Lean

But : qu'il ne reste aucun doute sur ce point : **le théorème démontré en Lean dit exactement « un graphe fortement
régulier de paramètres (99, 14, 1, 2) n'a aucun automorphisme d'ordre 3 », et sa preuve est acceptée par le noyau.**

## 1. Le seul fichier à lire : `c3formal/Challenge.lean`

98 lignes, commentaires compris. Il n'importe que trois modules de Mathlib, rien de ce projet, et ne contient **aucune
définition**. Il énonce 7 théorèmes, tous avec la preuve `sorry` :

| théorème | énoncé |
|---|---|
| `srg99_aut_cube` | pour tout graphe `G` avec `G.IsSRGWith 99 14 1 2` et tout automorphisme `σ : G ≃g G` tel que `σ (σ (σ v)) = v` pour tout `v`, on a `σ v = v` pour tout `v` |
| `srg99_no_orderOf_three` | pour un tel graphe, aucun `σ : G ≃g G` ne vérifie `orderOf σ = 3` |
| `srg99_three_not_dvd_card_aut` | pour un tel graphe, `¬ 3 ∣ Nat.card (G ≃g G)` : 3 ne divise pas l'ordre du groupe d'automorphismes |
| `srg99_elementary` | le premier énoncé **sans aucune bibliothèque de graphes** (voir §3) |
| `srg9_aut_cube_false` | le premier énoncé, avec (9, 4, 1, 2) à la place de (99, 14, 1, 2), est **faux** |
| `srg9_group_forms_false` | il existe un srg(9, 4, 1, 2) avec un automorphisme d'ordre 3, et 3 divise l'ordre de son groupe d'automorphismes |
| `srg9_elementary_false` | l'énoncé élémentaire, avec (9, 4, 1, 2) à la place de (99, 14, 1, 2), est **faux** |

Les preuves sont dans `c3formal/Solution.lean`. Celles des quatre énoncés `srg99_*` découlent de `C3.no_order3`
(`c3formal/C3formal/FixLemma.lean`), le théorème principal du projet. Celles des trois tests `srg9_*` sont des calculs sur
un graphe explicite à 9 sommets (section 5).

## 2. Ce que la machine garantit : `lake comparator`

`lake comparator` fait partie de Lake depuis Lean 4.35. Il prend un défi (`Challenge.lean`) et une solution
(`Solution.lean`), avec la configuration `c3formal/comparator.json`, et il établit que :

1. **les énoncés sont identiques.** Chaque théorème de la solution a exactement le même énoncé que dans le défi (même
   terme Lean, mêmes paramètres d'univers) ;
2. **les définitions sont identiques.** Toute constante dont dépendent ces énoncés (`SimpleGraph.IsSRGWith`,
   `SimpleGraph.commonNeighbors`, `Fintype.card`, `List.countP`, …, jusqu'au cœur de Lean) est la même, valeur comprise,
   dans le défi et dans la solution. La solution ne peut donc rien redéfinir ;
3. **les axiomes sont standard.** Les preuves n'utilisent aucun axiome hors de `propext`, `Quot.sound` et
   `Classical.choice`. Cela exclut `sorry`, `native_decide` (axiome `Lean.ofReduceBool`) et tout axiome ajouté ;
4. **le noyau accepte les preuves.** Le noyau de Lean rejoue la preuve dans un environnement vierge, depuis un export
   texte (format NDJSON de `leanexport`) qui contient la preuve et **toutes** ses dépendances : Mathlib et le cœur de
   Lean, donc pas seulement les fichiers du projet. Avec `--paranoid`, cinq autres vérificateurs livrés avec Lean doivent
   aussi l'accepter : `leanchecker-paranoid` (le noyau de Lean avec des contrôles supplémentaires), `lean4lean` (le noyau
   réécrit en Lean), `nanoda` (réimplémentation indépendante en Rust), `con-leche` (vérificateur écrit en Lean, accompagné
   d'un théorème de correction) et `con-ron` (son portage).

Le point 4 répond aussi aux deux autres réserves : un bogue du noyau, et la version de Lean utilisée, qui est une
pré-version (`v4.35.0-rc2`). Pour qu'une preuve fausse passe, il faudrait la même erreur dans le noyau C++ de Lean, dans
`lean4lean`, dans `nanoda` et dans `con-leche` et `con-ron`, qui sont des implémentations écrites séparément.

## 3. L'énoncé élémentaire : ne pas dépendre de Mathlib

`srg99_elementary` n'utilise aucune définition de Mathlib, seulement le cœur de Lean :

```lean
theorem srg99_elementary (adj : Fin 99 → Fin 99 → Bool)
    (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false)
    (h_deg : ∀ i, (List.finRange 99).countP (fun j => adj i j) = 14)
    (h_adj : ∀ i j, adj i j = true →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 1)
    (h_nonadj : ∀ i j, i ≠ j → adj i j = false →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 2)
    (σ : Fin 99 → Fin 99)
    (h_aut : ∀ i j, adj (σ i) (σ j) = adj i j)
    (h_cube : ∀ i, σ (σ (σ i)) = i) :
    ∀ i, σ i = i
```

Les sommets sont 0, …, 98 (`Fin 99`). `adj` est une matrice d'adjacence booléenne, symétrique et de diagonale nulle.
Chaque sommet a 14 voisins (`List.countP` compte les éléments de la liste `[0, …, 98]` qui vérifient la condition). Deux
sommets adjacents ont exactement 1 voisin commun, deux sommets distincts non adjacents en ont exactement 2. `σ` préserve
l'adjacence et la non-adjacence, et `σ ∘ σ ∘ σ = id`, donc `σ` est une bijection : un automorphisme d'ordre 1 ou 3.
Conclusion : `σ` est l'identité.

Cet énoncé et `srg99_aut_cube` sont démontrés tous les deux par le noyau. Un lecteur qui ne connaît pas Mathlib n'a qu'à
lire celui-ci.

## 4. Les définitions de Mathlib utilisées par les autres énoncés (textuellement)

```lean
structure SimpleGraph (V : Type u) where                 -- Combinatorics/SimpleGraph/Basic.lean
  Adj : V → V → Prop
  symm : Std.Symm Adj
  loopless : Std.Irrefl Adj

structure IsSRGWith (n k ℓ μ : ℕ) : Prop where           -- Combinatorics/SimpleGraph/StronglyRegular.lean
  card : Fintype.card V = n
  regular : G.IsRegularOfDegree k
  of_adj : ∀ v w, G.Adj v w → Fintype.card (G.commonNeighbors v w) = ℓ
  of_not_adj : Pairwise fun v w ↦ ¬G.Adj v w → Fintype.card (G.commonNeighbors v w) = μ

def commonNeighbors (v w : V) : Set V := G.neighborSet v ∩ G.neighborSet w
def IsRegularOfDegree (d : ℕ) : Prop := ∀ v : V, G.degree v = d      -- degree v = #(G.neighborFinset v)
abbrev Iso := RelIso G.Adj G'.Adj                        -- G ≃g G : bijections σ avec G.Adj (σ a) (σ b) ↔ G.Adj a b

instance : Group (r ≃r r) where                          -- Algebra/Order/Group/End.lean
  one := .refl r
  mul f₁ f₂ := f₂.trans f₁                               -- (f₁ * f₂) x = f₁ (f₂ x) : la composition
  inv := .symm
```

`Pairwise p` signifie `∀ v w, v ≠ w → p v w`. C'est la définition usuelle d'un srg(n, k, λ, μ). `orderOf σ` est l'ordre
de `σ` dans ce groupe. `Nat.card` est le cardinal d'un type ; il vaut 0 pour un type infini, et le théorème
`srg99_three_not_dvd_card_aut` établit donc au passage que le groupe est fini.

## 5. Non-vacuité : le test sur srg(9, 4, 1, 2)

Un énoncé mal formalisé peut être vrai pour une raison triviale : des hypothèses contradictoires, ou une conclusion qui
ne peut pas échouer. Les théorèmes `srg9_*` écartent ce risque. Le graphe de la tour 3 × 3 (deux cases sont adjacentes
si elles partagent une ligne ou une colonne) est un srg(9, 4, 1, 2), avec les mêmes λ = 1 et μ = 2. Le décalage des
lignes en est un automorphisme d'ordre 3. Donc les mêmes formules, avec (9, 4, 1, 2), sont fausses : les hypothèses
peuvent être satisfaites et la conclusion peut échouer. Les vérifications sur ce graphe sont faites par `decide`, par
le noyau, pas par du code compilé.

## 6. Exécutions

**Machine d'origine** (Windows 11, 2026-09-23 à 17:15), `lake comparator --paranoid` : **« Your solution is okay! »**.
Journal complet : `logs/comparateur_local_2026-09-23.log`.

| étape | résultat | durée |
|---|---|---|
| compilation et export du défi | OK | 6 s |
| compilation et export de la solution | OK : 26 582 déclarations, preuve et dépendances (145 Mo) | 17 s |
| comparaison des 7 énoncés et de leurs définitions | identiques | — |
| axiomes | `propext`, `Quot.sound`, `Classical.choice` uniquement | — |
| `leanchecker-paranoid` | accepte | 19 s |
| `lean4lean` | accepte | 21 s |
| `nanoda` | accepte | 4 s |
| `con-leche` (mode `--verified`) | accepte 26 552 déclarations | 13 s |
| `con-ron` (mode `--verified`) | accepte 26 552 déclarations | 18 s |
| noyau de Lean | accepte | 16 s |

Le mode `--verified` de `con-leche` est celui de son théorème de correction (`ConLeche.no_proof_of_False`, d'après sa
documentation) : si le vérificateur accepte le flux de déclarations dans ce mode, l'environnement obtenu ne contient
aucune constante de type `False`. `con-ron`, son portage, reprend le même mode.

Sous Windows, le bac à sable de `lake comparator` (`bwrap`) n'existe pas. Il faut donc `--inadvisably-no-sandbox`, et Lake
prévient que le verdict « n'est pas fiable ». Le bac à sable protège contre du code malveillant *exécuté pendant la
compilation* ; les contrôles eux-mêmes sont identiques. D'où la seconde exécution :

**Machine Linux neuve de GitHub, avec bac à sable** (2026-09-23, run 35880776817 : 2 cœurs, 7 Go de RAM), à partir du
seul contenu du dépôt (commit `874903f`, workflow `.github/workflows/lean-verify.yml`). Journal :
`logs/github_actions_run_35880776817.log`.

| étape | résultat | durée |
|---|---|---|
| cache Mathlib, puis compilation de `C3formal`, `Challenge` et `Solution` | OK | 3 min 13 |
| `C3formal/Check.lean` (axiomes des énoncés intermédiaires) | `propext`, `Classical.choice`, `Quot.sound` | 3 s |
| `lake comparator` | **« Your solution is okay! »** | 44 s |
| `lake comparator --paranoid` | les six vérificateurs acceptent ; `con-leche` et `con-ron` : 26 552 déclarations (`--verified`) ; **« Your solution is okay! »** | 2 min 43 |

Le nombre de déclarations acceptées est le même que sur la machine d'origine : la compilation propre a produit la même
preuve.

Un premier passage (17:01, `logs/comparateur_local_2026-09-23_essai1.log`) s'était arrêté sur `con-leche` : le lanceur
limitait alors la mémoire *engagée* à 5 Go. Or `con-leche` engage environ 5,6 Go (1 Gio de pile réservée par travailleur)
pour environ 1 Go de RAM réelle. C'était un manque de ressources, pas un rejet (`logs/con-leche_local_2026-09-23.log`).

## 7. Ce qui reste hors de la machine

- **Lire `Challenge.lean`** et vérifier que ses énoncés disent bien ce qu'on veut. Les sections 3 et 4 ci-dessus en
  donnent les clés ; quelques minutes.
- **Les résultats publiés utilisés au-delà de Lean** (section 9), qui ne sont pas formalisés ici. Avec Makhnev–Minakova
  (|Aut Γ| divise 2·3³·7·11) et Cesarz–Woldar (si |Aut Γ| est pair, il divise 6 ; si 7 le divise, Aut Γ ≅ ℤ₇), tous deux
  sans ordinateur, on obtient |Aut Γ| ∈ {1, 2, 7, 11}. Si l'on admet aussi le calcul par ordinateur de Behbahani–Lam
  (seuls 2 et 3 peuvent diviser |Aut Γ|), on obtient |Aut Γ| ∈ {1, 2} : Aut Γ est trivial ou ℤ₂.
- **La preuve mathématique lisible** (`pdf/preuve_c3.pdf`) sert à la compréhension et à une éventuelle publication. Sa
  correction ne conditionne pas celle du théorème Lean.

## 8. Reproduire

Sous Linux, où le bac à sable `bwrap` du comparateur est disponible :

```
cd c3formal
lake exe cache get
lake build C3formal Challenge Solution
lake comparator --paranoid          # attendu : « Your solution is okay! »
```

Le même contrôle tourne sur GitHub Actions, sur une machine Linux neuve, à chaque modification de `c3formal/`
(`.github/workflows/lean-verify.yml`).

## 9. État de la littérature sur les automorphismes (vérifié le 2026-09-23)

| référence | résultat sur Aut(Γ) | méthode |
|---|---|---|
| Makhnev–Minakova, 2004 | \|Aut Γ\| divise 2·3³·7·11 ; un automorphisme d'ordre 3 fixe l'ensemble vide ou un triangle | caractères |
| Behbahani, thèse 2009 (th. 4.14) ; Behbahani–Lam, Discrete Math. 2011 | seuls 2 et 3 peuvent diviser \|Aut Γ\| ; un automorphisme d'ordre 3 n'a pas de point fixe. Le cas « ordre 3 sans point fixe » est marqué « ? » (table 21 de la thèse) : non tranché | ordinateur |
| Lou–Murin, rapport MIT PRIMES, 2014 | pas d'automorphisme d'ordre 11, 13, ni d'ordre premier > 14 | élémentaire |
| Crnković–Maksimović, Contrib. Discrete Math. 2020 | aucun groupe d'automorphismes d'ordre 6 ou 9 (ℤ₆, S₃, ℤ₉, E₉) ; un ℤ₃ seul n'est pas exclu | ordinateur |
| Cesarz–Woldar, Algebraic Combinatorics 2025 | si 2 divise \|Aut Γ\|, il divise 6 ; si 7 le divise, Aut Γ ≅ ℤ₇ | sans ordinateur |
| Ishida, arXiv:2606.29183 (juillet 2026) | ordre 3 : Fix = ∅ et a₁ = 18, ou Fix = triangle et a₁ = 6 ; non exclu | identité trace–rang |
| Thakkar–Severini, arXiv:2608.11211 (v2, 18 septembre 2026) | « The fixed-point-free ℤ3 model, with 33 orbits, likewise remained unknown within 1800 seconds » | CP-SAT |

Avant ce travail, en réunissant ces résultats (dont ceux obtenus par ordinateur), |Aut Γ| ∈ {1, 2, 3}, et le seul cas
ouvert était un automorphisme d'ordre 3 sans point fixe. Aucune source trouvée ne l'exclut. Le théorème formalisé ici
l'exclut, sans calcul sur ordinateur, et exclut aussi, sans ordinateur, le cas avec points fixes. D'où |Aut Γ| ∈ {1, 2}
(section 7).

Limite de cette recherche : arXiv, moteurs de recherche, revues en ligne et une requête en russe. Un travail non indexé,
en cours d'évaluation, ou publié seulement dans une revue russe non numérisée pourrait avoir échappé.
