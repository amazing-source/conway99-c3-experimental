# c3formal — formalisation Lean 4 (branche C3 de Conway 99)

Statut : **vérifié par Lean**, sans `sorry` (Lean v4.35.0-rc2, Mathlib `v4.35.0-rc2`), **sans aucune entrée extérieure**.
Pour chaque énoncé ci-dessous, `#print axioms` → `[propext, Classical.choice, Quot.sound]`, c'est-à-dire les axiomes
standard de Lean/Mathlib (voir `C3formal/Check.lean`, sortie dans `../logs/lean_axioms_final.log`).

## Énoncé final

```lean
theorem C3.no_order3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v) : ∀ v, σ v = v
```

Tout automorphisme σ d'un graphe fortement régulier de paramètres (99, 14, 1, 2) tel que σ³ = 1 est l'identité :
**le graphe n'a aucun automorphisme d'ordre 3** (corollaire 3 du PDF). `G.IsSRGWith 99 14 1 2` est la définition de
Mathlib d'un graphe fortement régulier ; `σ : G ≃g G` est un automorphisme de graphe.

## Étapes vérifiées

| énoncé Lean | contenu | PDF |
|---|---|---|
| `C3.no_order3` (`FixLemma.lean`) | tout automorphisme σ avec σ³ = 1 est l'identité | corollaire 3 |
| `C3.no_order3_fix_le3` (`TriangleGraph.lean`) | aucun automorphisme d'ordre 3 avec **au plus 3 points fixes** | th. 1 + prop. 2 |
| `C3.no_free_order3` (`Graph.lean`) | aucun automorphisme d'ordre 3 **sans point fixe** | théorème 1 |
| `C3.no_triangle_order3` (`TriangleGraph.lean`) | aucun automorphisme d'ordre 3 avec **exactement 3 points fixes** | proposition 2 |
| `C3.no_pair` (`Main.lean`) | le théorème matriciel (33 × 33) | théorème 5 |
| `C3.Tri.no_triangle_pair` (`TriangleStep4.lean`) | la version matricielle du cas du triangle (32 + 3) | §4 |

Remarques :
- Points fixes (`FixLemma.lean`, lemme 7 du PDF) : un automorphisme σ ≠ 1 avec σ³ = 1 a au plus 3 points fixes. C'est
  le résultat de Makhnev–Minakova (« vide ou un triangle »), redémontré ici par un comptage élémentaire (fermeture par
  λ = 1 et μ = 2, nombre de voisins fixes dans {2, 8, 14}, comptage des arêtes entre points fixes et non fixes).
- `no_triangle_order3` suppose seulement « exactement 3 points fixes » ; que ces points forment un triangle est
  démontré (`fixed_adj`).
- L'identité d'Ishida n'intervient nulle part (voir `TriangleMatrix.lean`).

## Ce qu'un relecteur doit contrôler (la « base de confiance »)
Le fichier `Challenge.lean`, et lui seul. Il n'importe que Mathlib, ne contient aucune définition, et énonce le résultat
sous plusieurs formes (graphe, groupe, matrice booléenne sans Mathlib), plus un test de non-vacuité sur srg(9, 4, 1, 2).
`Solution.lean` démontre ces énoncés à partir de `C3.no_order3`. `lake comparator` (configuration `comparator.json`)
vérifie que les énoncés sont identiques, que les axiomes sont standard, et que le noyau de Lean et cinq vérificateurs
indépendants acceptent les preuves. Détails et résultats : `../AUDIT_ENONCE.md`. (Pour les énoncés matriciels
intermédiaires : `Eis.lean`, `J`, `φ3`, `At`, `Jw`, `wt`.)

## Fichiers (dans l'ordre logique)
| fichier | contenu |
|---|---|
| `Eis.lean` | ℤ[ω] : anneau, conjugaison, réduction `ρ` |
| `EisEuclid.lean` | norme, division euclidienne : ℤ[ω] intègre et principal |
| `EisComplex.lean` | plongement dans ℂ ; `det (B* B)` entier > 0 si `B` a un inverse à gauche |
| `Saturated.lean`, `SaturatedGen.lean` | étape 2 (bases de noyaux saturés, via Smith) et étape 3 (`N = B K B*`, `G K = c I`) |
| `Step5.lean` | **étape 5** : `r = r'` et `det G ≡ det G' (mod 3)` |
| `NumberTheory.lean` | `v₁₁` impair ⇒ `d ≡ 2` ; diviseur positif de `7^r` ⇒ `≡ 1` |
| `IntPart.lean` | étapes 1, 3, 4 côté ℤ : `det G ≡ 2 (mod 3)` (réseau `W`, rang `r_W = r + 1`, `33 d = det(T)² det G_W`) |
| `Main.lean` | côté ℤ[ω] (`det G' ≡ 1`) et **théorème matriciel `no_pair`** |
| `Bridge.lean` | lemme 4 : matrice d'adjacence invariante par décalage ⇒ couple `(Q, M)` |
| `Graph.lean` | réétiquetage `V ≃ Fin 33 × ZMod 3` ; **théorème 1** `no_free_order3` |
| `GenLemmas.lean` | versions « taille quelconque » de l'étape 5, du côté ℤ[ω] et du lemme 11-adique |
| `TriangleMatrix.lean` | cas du triangle : `Ã`, poids `w`, symétrie de `D Ã`, `wᵀ Ã = 14 wᵀ` |
| `TriangleMain.lean` | `N = 11(Ã + 4I) - 2 𝟙 wᵀ` ; ses lignes fixes sont ≡ 0 (mod 3) |
| `TriangleStep5.lean` | coordonnées fixes divisibles par 3, Gram pondéré `G̃` entier, `G̃ K = 77 I`, `det G̃ ≡ 1 (mod 3)` |
| `TriangleStep4.lean` | `det G̃ ≡ 2 (mod 3)` (`𝟙ᵀ D 𝟙 = 99`) ; **`no_triangle_pair`** |
| `TriangleBridge.lean` | lemme 4, version triangle (matrices `E`, `R`, `E_ω`) |
| `TriangleGraph.lean` | réétiquetage `V ≃ (Fin 32 × ZMod 3) ⊕ Fin 3`, `fixed_adj`, **proposition 2**, `no_order3_fix_le3` |
| `FixLemma.lean` | lemme des points fixes (au plus 3) et **énoncé final `no_order3`** |
| `Check.lean` | `#print axioms` des énoncés |
| `../Challenge.lean` | **l'énoncé seul** (n'importe que Mathlib, preuves `sorry`) |
| `../Solution.lean` | les mêmes théorèmes, démontrés à partir de `C3.no_order3` |
| `../comparator.json` | la configuration de `lake comparator` : les 7 théorèmes, les axiomes permis |

## Reproduire
```
cd c3formal
lake exe cache get      # cache Mathlib
lake build              # compile tout (~2240 tâches ; quelques minutes une fois le cache présent)
lake env lean C3formal/Check.lean   # affiche les axiomes utilisés
lake build Challenge Solution
lake comparator --paranoid          # Linux (bac à sable bwrap) ; attendu : « Your solution is okay! »
```
