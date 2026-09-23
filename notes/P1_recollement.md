# P1 — Obstruction par les discriminants : srg(99,14,1,2) n'a pas d'automorphisme d'ordre 3

Statut : **DÉRIVÉ** (preuve écrite ci-dessous) + **OBSERVÉ** (lemme général testé sur graphes réels et ~1 660 réseaux
aléatoires, 0 violation) + **vérifié par machine** (Lean 4 / Mathlib, voir § 0 quater : théorème 1 et proposition 2, depuis la
définition d'un srg). Attend une relecture humaine. Rien de ceci n'est dans le dépôt conway99-c3.

## 0. Énoncé

**Théorème (DÉRIVÉ, vérifié en Lean).** Aucun srg(99,14,1,2) n'a d'automorphisme d'ordre 3 sans point fixe, ni
d'automorphisme d'ordre 3 ayant exactement trois points fixes (ceux-ci formeraient un triangle). Comme le nombre de points
fixes est ≡ 99 ≡ 0 (mod 3) : aucun automorphisme d'ordre 3 n'a au plus trois points fixes.

Avec Makhnev–Minakova 2004 (ÉTABLI, littérature : Fix(g) est vide ou un triangle), **srg(99,14,1,2) n'a aucun automorphisme
d'ordre 3**. La branche C3 est vide, sans calcul par solveur et sans la recherche par ordinateur de Behbahani–Lam.

Origine de l'idée (HEURISTIQUE) : la preuve de tau = 6 lit la *trace* du module libre E_3·Z_3^99 ≅ Z_3[C3]^18. L'invariant
suivant d'un module hermitien libre est son *discriminant*, qui vit dans Z_3[C3]^× ; ses deux spécialisations (caractère
trivial = quotient Q, caractère ω = matrice d'Eisenstein M) sont donc congrues modulo 3. Ishida (arXiv:2606.29183v2) n'utilise
que l'identité trace = rang ; le raffinement par déterminant n'y figure pas (texte extrait dans `data/ishida_text.txt`).

## 0 quater. Cas du triangle sans Ishida, et statut Lean (2026-09-23, soir)

**Triangle (DÉRIVÉ, vérifié en Lean).** Trois points fixes t_i, 32 orbites libres. Sur les invariants (Z^35), A agit par
Ã = [[Q, a], [3aᵀ, J₃ − I₃]], Ã1 = 14·1, Ã² + Ã = 12I + 2·1wᵀ, w = (3,…,3,1,1,1), D = diag(w) (DÃ symétrique),
Δ = diag(I₃₂, 3I₃) (DΔ = 3I).
1. Ñ = 11(Ã + 4I) − 2·1wᵀ : (Ã − 3I)Ñ = 0, Ñx = 77x sur ker(Ã − 3I) ; lignes fixes ≡ 0 (mod 3)
   (Ñ[t,U] = 33a − 6, Ñ[t,t'] = 9 + 33δ) ⇒ 3 | x_t pour tout x ∈ L = ker_Z(Ã − 3I).
2. G̃ = BᵀDB/3 entier ; X = ÑΔ symétrique, DX = 3Ñᵀ, X = BKBᵀ, K = CXCᵀ ; G̃K = 77I.
3. Modulo 3 : X ≡ diag(2(Q̄ + I), 0), B̄ = (B̄₁ ; 0) ⇒ seules les 32 orbites libres interviennent ⇒ étape 5 telle quelle :
   r = r' et det G̃ ≡ d' ≡ 1. (C'est ce point qui remplace l'identité trace–rang d'Ishida pour obtenir r = r'.)
4. W = ker_Z((Ã − 3)(Ã − 14)) ⊇ L ⊕ Z1 ; N_W = 9(Ã + 4I) − 1wᵀ = 63 × projecteur ; G_W K_W = 189I ⇒ 11 ∤ det G_W ;
   Gram_D([B | 1]) = diag(3G̃, 99) ⇒ 3^r · 99 · det G̃ = det(T)² det G_W ⇒ v₁₁ impair ⇒ det G̃ ≡ 2. Contradiction.
Le triangle n'est pas une hypothèse : avec exactement 3 points fixes, deux points fixes non adjacents auraient μ = 2 voisins
communs fixés, soit ≥ 4 points fixes.

**Lean (c3formal/, Mathlib v4.35.0-rc2), sans `sorry`, axiomes [propext, Classical.choice, Quot.sound] :**
`C3.no_free_order3` (théorème 1), `C3.no_triangle_order3` (proposition 2, « exactement 3 points fixes »),
`C3.no_order3_fix_le3` (au plus 3 points fixes), plus les formes matricielles `C3.no_pair`, `C3.Tri.no_triangle_pair`.
~~Seule entrée non formalisée de « aucun automorphisme d'ordre 3 » : Makhnev–Minakova.~~ Remplacée (même soir) :

**Points fixes sans Makhnev–Minakova (DÉRIVÉ, vérifié en Lean, `FixLemma.lean`).** g ≠ 1, g³ = 1, F = Fix(g), n_x = nombre
de voisins fixes de x ∈ F. (1) Un sommet adjacent à deux points fixes est fixe (λ = 1 ; μ = 2 et ordre 3) ; donc un sommet
non fixe a ≤ 1 voisin fixe. (2) n_x ≡ 14 (mod 3) (orbites) et n_x pair (appariement λ = 1) ⇒ n_x ∈ {2, 8, 14}.
(3) Σ_F (14 − n_x) ≤ 99 − |F|. (4) n_x = 14 ⇒ g = 1 ; n_x = 8 ⇒ 15(9 + s) ≤ 123 + 10s, impossible ; tous n = 2 ⇒ |F| ≤ 3.
Avec le théorème 1 et la proposition 2 : **`C3.no_order3`** (tout σ avec σ³ = 1 est l'identité), axiomes standard seulement.

## 0 bis. Preuve élémentaire (version principale, la plus facile à relire)

Cadre : g sans point fixe, orbites (U,b), U = 1..33 ; Q quotient (Q_UV = Σ_b A[(U,0),(V,b)]) ; M matrice d'Eisenstein
(M_UV = Σ_b A[(U,0),(V,b)] ω^b). Clé : **Q ≡ M (mod π) entrée par entrée**, π = 1 − ω, car ω ≡ 1 (mod π).
E_3 = (A+4I)/7 − 2J/77 agit sur les vecteurs invariants (coordonnées d'orbites) comme P^Q = (Q+4I)/7 − 6J/77, projecteur
orthogonal sur V_3(Q), et sur la composante ω comme P^M = (M+4I)/7, projecteur orthogonal sur V_3(M). Les deux sont 3-entiers et
**P^Q ≡ P^M ≡ Q + I** (mod 3, resp. mod π).

1. L_1 := P^Q(Z_3^33) = Z_3^33 ∩ V_3(Q) est facteur direct orthogonal de Z_3^33, donc unimodulaire. Il est engendré par les
   P^Q e_U, de Gram P^Q ; sa réduction L_1/3L_1 est donc l'espace quadratique (F_3^33 / rad P̄, P̄), P̄ = (Q + I) mod 3.
2. De même L_ω := P^M(Z_3[ω]^33) est unimodulaire (hermitien) ; comme Z_3[ω]/π = F_3 et que la conjugaison y est triviale, sa
   réduction est l'espace quadratique (F_3^33 / rad P̄', P̄') avec P̄' = (M + I) mod π = P̄. **C'est le même espace.**
3. Le discriminant de la réduction d'un réseau unimodulaire est la réduction de son déterminant. Donc
   det L_1 ≡ det L_ω (mod 3), c'est-à-dire d_1 ≡ d_ω (mod 3) (et au passage dim V_3(Q) = dim V_3(M) = 18 : c'est tau = 6).
4. Or d_1 = 7^a·11 ≡ 2 et d_ω = 7^j ≡ 1 (§3 ci-dessous). Contradiction. ∎

En une phrase : **la forme quadratique (Q + I) mod 3, de rang 18, devrait avoir pour discriminant 2 (vu depuis l'arithmétique
entière de Q, à cause du facteur 11 de ⟨1,1⟩ = 33) et 1 (vu depuis celle de M, qui ne fait intervenir que 7).**
Contrôle (OBSERVÉ, `scripts/glue_fp.py`, `logs/glue_fp.log`) : sur T(6)…T(18), T(7), T(10), T(13), le rang et le discriminant
de la forme P̄ sur F_3 coïncident avec ceux des deux réseaux, y compris dans un cas réel de discriminant 2 (T(10), λ = 6).

Cette version s'étend telle quelle à p premier quelconque (action libre, projecteur p-entier) : (d_1 / p) = (d_ζ mod π / p)
(symboles de Legendre), puisque les deux réductions sont le même espace quadratique sur F_p.

## 0 ter. Version « pure algèbre linéaire » (sans p-adiques ; la plus formalisable, par ex. en Lean)

**Énoncé matriciel.** Il n'existe pas de couple (Q, M) avec
- Q ∈ M_33(Z) symétrique, Q·**1** = 14·**1**, Q² + Q = 12I + 6J ;
- M ∈ M_33(Z[ω]) hermitienne, M² + M = 12I ;
- Q ≡ M modulo (1 − ω), entrée par entrée.

(Un automorphisme d'ordre 3 sans point fixe fournit un tel couple : Q = A(1), M = A(ω), où A(x) = Σ_b A_b x^b est la matrice
33×33 à coefficients dans Z[C3] ; A ↦ A(x) est un morphisme d'anneaux et J_99 ↦ (1+x+x²)J_33. On n'utilise ni tau, ni les valeurs 0/1/2.)

**Preuve.**
- S1. P := (Q+4I)/7 − (6/77)J et P' := (M+4I)/7 sont les projecteurs orthogonaux sur ker(Q−3I) et ker(M−3I) (calcul direct à partir
  des équations, avec QJ = 14J, J² = 33J).
- S2. L := Z^33 ∩ ker(Q−3I) est saturé, donc a une base B (33×r) avec C ∈ M_{r×33}(Z), CB = I. Si G := BᵀB, alors P = B G⁻¹ Bᵀ et
  **C P Cᵀ = G⁻¹**. Idem sur Z[ω] (principal) : B', C', G' := B'*B', C' P' C'* = G'⁻¹.
- S3. 77P est entière, donc 77·G⁻¹ aussi, donc d := det G divise 77^r : **d = 7^a·11^b**. 7P' est entière, donc d' := det G' (un entier
  > 0) divise 7^{r'} : **d' = 7^j ≡ 1 (mod 3)**.
- S4. W := Z^33 ∩ (ker(Q−3I) ⊕ Q·**1**) a pour projecteur (Q+4I)/7 − J/21, sans 11 au dénominateur, donc 11 ∤ det(W) (même argument
  que S2–S3). L ⊕ Z·**1** ⊂ W avec ⟨**1**,**1**⟩ = 33 : [B | **1**] = B_W·T, T entière, donc 33·d = det(W)·det(T)², d'où b + 1 = 2·v_11(det T) :
  **b est impair**, donc **d ≡ 11^b ≡ 2 (mod 3)**.
- S5. Modulo 3 (et modulo π = 1−ω, de corps résiduel F_3, conjugaison triviale) : 7 ≡ 1 et 6/77 ≡ 0, donc P̄ = P̄' = (Q+I) mod 3.
  En réduisant S2 : C̄ P̄ C̄ᵀ = Ḡ⁻¹ et P̄ = B̄'·Ḡ'⁻¹·B̄'ᵀ, donc r = rang P̄ = r' et
  d⁻¹ = det(C̄ P̄ C̄ᵀ) = det(C̄ B̄')² · d'⁻¹ dans F_3. Les carrés non nuls de F_3 valent 1 : **d ≡ d' (mod 3)**.
- S6. 2 ≡ 1 (mod 3) : contradiction. ∎ (Bonus : r = r' donne (2τ+114)/7 = (132−τ)/7, soit τ = 6.)

## 1. Lemme de recollement (cas libre), version « module hermitien sur Z_3[C3] »

G = ⟨g⟩ ≅ C3 agit librement sur X, |X| = 3m, points (U,b), g(U,b) = (U,b+1). R = Z_3[G] (local). ω = e^{2iπ/3}.
V ⊂ Q^X G-stable, de projecteur orthogonal P **3-entier**.
- V_1 ⊂ Q^m : partie invariante en coordonnées d'orbites ; projecteur P^Q_{UV} = Σ_b P[(U,0),(V,b)].
- V_ω ⊂ Q(ω)^m : composante ω-isotypique (f(U,b) = ω^b c_U) ; projecteur P^M_{UV} = Σ_b P[(U,0),(V,b)] ω^b.
- d_1 = det(Z^m ∩ V_1), d_ω = déterminant hermitien de Z[ω]^m ∩ V_ω (entiers > 0).

**Lemme (DÉRIVÉ, OBSERVÉ).** d_1 et d_ω sont premiers à 3 et d_1 ≡ d_ω (mod 3).

*Preuve.*
1. F := P·Z_3^X = Z_3^X ∩ V_{Q_3} est facteur direct du R-module libre Z_3^X ≅ R^m, donc projectif, donc libre (R local) : F ≅ R^r.
2. H(x,y) := Σ_{h∈G} b(hx, y)·h ∈ R (b produit scalaire standard) : forme hermitienne sur F (involution h ↦ h⁻¹).
3. Soit H ∈ M_r(R) sa matrice dans une R-base. Les spécialisations ε : g ↦ 1 et χ : g ↦ ω donnent :
   - F ⊗_ε Z_3 = F/(g−1)F, engendré par les images des P e_{(U,0)}, de Gram P^Q ; libre de rang r, forme non dégénérée
     (rang P^Q = r), donc isométrique à P^Q(Z_3^m) = Z_3^m ∩ V_1 : déterminant d_1 (à un carré de Z_3^× près).
     [Détail : les deux quotients de Z_3^m par le noyau de la Gram coïncident, car un Z_3-module libre de rang r ne se
     surjecte sur Z_3^r que par un isomorphisme.]
   - F ⊗_χ Z_3[ω] : Gram conj(P^M), isométrique (au conjugué près) à Z_3[ω]^m ∩ V_ω : déterminant d_ω (à une norme près).
4. ε et χ coïncident modulo l'idéal maximal (g ↦ 1 dans F_3) : det ε(H) ≡ det χ(H) dans F_3.
5. Changer de base multiplie ces déterminants par u² ou u·ū, qui valent 1 dans F_3 ; les deux sont des unités (réseaux
   unimodulaires en 3, car P^Q et P^M sont des projecteurs orthogonaux 3-entiers). ∎

## 2. Extension aux points fixes (pour le cas « triangle fixe »)

Si g a des points fixes, Z_3^X = R^{m} ⊕ Z_3^{f}, et F = P·Z_3^X ≅ R^α ⊕ Z_3^β, où β = rang_{F_3}(P[Fix] mod 3) (quotient de
Brauer ; ÉTABLI chez Ishida, et direct par la cohomologie de Tate : Ĥ⁰(G,F) = image de P sur Ĥ⁰(G,Z_3^X) = F_3^{Fix}).
**Si β = 0, F est libre** et le lemme s'applique avec :
- d_1 := det_b((Z^X)^G ∩ V) / 3^r (car F^G = N·F ≅ F_G avec b = 3·H(1)) ;
- d_ω := det(Z[ω]^m ∩ V_ω), où seuls les points des orbites libres interviennent (un point fixe n'a pas de composante ω,
  et en ω les chemins passant par un point fixe sont multipliés par 1+ω+ω² = 0).
(DÉRIVÉ ; OBSERVÉ : `scripts/glue_fixed.py`, 318 cas β = 0, 0 violation, et v_3(det) = r à chaque fois.)

## 3. Application à srg(99,14,1,2)

A² + A = 12I + 2J, spectre 14, 3^54, (−4)^44. E_3 = (A + 4I)/7 − 2J/77 est 3-entier (ÉTABLI dans C3), et E_3 ≡ A + I − J (mod 3).

**Quel β ?** Fix(g) = ∅ : β = 0. Fix(g) = triangle : E_3[Fix] ≡ (J − I) + I − J = 0 (mod 3), donc β = 0 aussi.
(Plus généralement β = 0 ⟺ Fix(g) est une clique, donc de taille 0 ou 3 puisque λ = 1.)

**(a) d_ω = 7^j ≡ 1 (mod 3).** V_ω = V_3(M) avec M² + M = 12I (le terme J s'annule en ω). S = Z[ω]^m ∩ V_3(M) ;
Z[ω]^m est unimodulaire, donc S^# = P^M(Z[ω]^m), et 7·P^M = M + 4I est entière : S^#/S est tué par 7, d'ordre d_ω².

**(b) d_1 = 7^a · 11 ≡ 2 (mod 3).** Cas libre : S_1 = Z^33 ∩ V_3(Q) ; 77·P^Q = 11(Q+4I) − 6J : seuls 7 et 11 interviennent.
En 11 : le projecteur sur V_{−4}(Q), I − (Q+4I)/7 + J/21, est 11-entier, donc Z_11^33 = (Z_11^33 ∩ V_{−4}) ⊥ W, avec W
unimodulaire contenant **1**, primitif, de norme 33. Or Z_11^33 ∩ V_3(Q) = 1^⊥ ∩ W a pour déterminant 33 (à une unité près) :
v_11(d_1) = 1. Cas triangle fixe : le même raisonnement sur (Z^X)^G (unimodulaire hors de 3) avec b(1,1) = 99 donne
v_11 = 1 ; en 3, det = 3^18 × unité ; seuls 3, 7, 11 interviennent. D'où d_1 ≡ 7^a·11 ≡ 2 (mod 3) dans les deux cas.

**(c) Contradiction.** Le lemme exige d_1 ≡ d_ω (mod 3), soit 2 ≡ 1. ∎

Mécanisme : la seule asymétrie entre les caractères est le vecteur **1**, qui ne vit que dans la partie triviale. Sa norme
33 = 3·11 injecte 11, qui n'est pas un carré modulo 3. Rien ne peut compenser, puisque le seul autre premier en jeu,
r − s = 7, est ≡ 1 (mod 3) (décomposé dans Z[ω]).

## 4. Tests (OBSERVÉ)
| test | résultat |
|---|---|
| T(6), T(9), T(12), T(15), T(18), T(21) (σ produit de 3-cycles, λ = −2) ; T(7), T(10), T(13) (λ 3-entier) | congruence vérifiée partout ; (2,2) réel : T(10), d_1 = 2⁸·5, d_ω = 2⁹ |
| mêmes graphes, λ non 3-entier | la congruence échoue (T(6) λ=2, T(9) λ=5, T(10) λ=−2, T(13) λ=−2) : le test sait détecter |
| recalcul indépendant (sympy + Smith) T(6), T(9), T(12) | valeurs identiques |
| sous-espaces aléatoires, action libre | 1 340 cas valides, 0 violation (505 cas (2,2)) |
| sous-espaces aléatoires avec points fixes, β = 0 | 318 cas, 0 violation |
| formule « premiers de r−s × premiers J » | exacte sur T(15) (7·13⁴ / 13⁵), T(18) (2¹⁹·17 / 2²⁴), T(21) (2·5·19⁶ / 19⁷) |
| T(18) : premier J = 17 ≡ 2 (mod 3), exposant 1, comme 11 pour Conway | compensé par 2¹⁹ (2 divise r − s = 16) : cohérent |

Critère général pour srg (`scripts/criterion_scan.py`) : T(n) jamais exclu à tort (3 | n ≤ 300) ; pour v ≤ 1300, 7 jeux de
paramètres exclus, tous d'existence inconnue chez Brouwer (« ? »).

## 5. À relire en priorité (un humain)
1. Étape 3 du lemme (identification des spécialisations avec les réseaux Z_3^m ∩ V_1 et Z_3[ω]^m ∩ V_ω).
2. Le calcul 11-adique (b) et l'absence d'autres premiers.
3. Cas triangle fixe : β = 0 et la normalisation d_1 = det/3^r. (Remplacé par l'argument élémentaire du § 0 quater,
   vérifié en Lean ; reste à relire à la main le point 1 de ce §.)
4. La dépendance à Makhnev–Minakova (Fix vide ou triangle), seule entrée extérieure.
