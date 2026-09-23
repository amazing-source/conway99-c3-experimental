# Journal du laboratoire c3_experimental

## 2026-09-23 — ouverture
- Contexte lu (lecture seule) : `c3_recherche_annexe/rapport/audit_c3.tex`, `plan_calcul.tex`. Rien écrit dans le dépôt.
- Consigne reçue tronquée (§3 à §11 manquants) ; appliqué : exploration libre, statuts explicites, isolation.
- venv local `.venv` (numpy 2.5.3, sympy 1.14, networkx 3.7, python-sat).

## P1 — obstruction par les discriminants (voir notes/P1_recollement.md)
- Idée née en cherchant « l'invariant après le rang » : l'argument tau = 6 utilise la trace du module libre
  E_3·Z_3^99 ≅ Z_3[C3]^18 ; l'invariant suivant est son discriminant hermitien, qui vit dans Z_3[C3]^×,
  d'où une congruence entre les deux spécialisations x=1 (quotient Q) et x=ω (matrice d'Eisenstein M).
- Calcul pour Conway 99 : d_1 = 7^a·11 ≡ 2 (mod 3) (le 11 vient de la norme 33 du vecteur 1),
  d_ω = 7^j ≡ 1 (mod 3). Contradiction ⇒ pas d'automorphisme d'ordre 3 sans point fixe. **[PREUVE?]**
- Tests du lemme général (tous passés) **[EMP]** :
  - T(6), T(9), T(12) (action libre, λ = −2) : congruence vérifiée ; échoue bien quand le projecteur n'est pas
    3-entier (le test détecte les violations). `logs/glue_T.log`
  - recalcul indépendant (sympy + forme de Smith, sans mon noyau entier) : mêmes valeurs. `logs/glue_crosscheck.log`
  - 283 sous-espaces G-stables aléatoires à projecteur 3-entier : 0 violation (174 cas (1,1), 109 cas (2,2)).
    `logs/glue_random_1.log`
- Critère général pour srg (p = 3), `scripts/criterion_scan.py` :
  - T(n), 3 | n, 6 ≤ n ≤ 300 : jamais exclu à tort (l'accord dépend de la parité de n : non trivial).
  - v ≤ 1300 : exclut une action libre d'ordre 3 pour 7 jeux de paramètres seulement :
    (99,14,1,2), (105,52,21,30), (105,52,29,22), (261,52,11,10), (714,248,97,80), (1221,610,279,330),
    (1221,610,329,280). **Tous sont « ? » (existence inconnue) chez Brouwer** (tables copiées dans `data/`).
    Aucun conflit avec un graphe connu.

## Suite du 2026-09-23 (consigne complète reçue : étiquettes ÉTABLI/DÉRIVÉ/OBSERVÉ/CONJECTURE/HEURISTIQUE/SPÉCULATION/RÉFUTÉ)
- Lecture seule du dépôt : README, LISEZMOI, rapport ; jamais de discriminant, réseau propre ni rang modulaire (hors trace) dans C3.
- Ishida (texte extrait, data/ishida_text.txt) : uniquement l'identité trace = rang ; pas de déterminant. Cesarz–Woldar 2023
  (arXiv:2308.02978) : l'ordre 3 reste ouvert dans la littérature.
- OBSERVÉ : 1 057 cas aléatoires de plus (graine 7), 0 violation ; T(7), T(10), T(13) cohérents ; cas réel (2,2) : T(10).
- DÉRIVÉ + OBSERVÉ : extension aux points fixes quand le quotient de Brauer est nul (β = 0) ; 318 cas aléatoires, 0 violation.
  Pour Conway 99, β = 0 ⟺ Fix est une clique (∅ ou triangle) : le cas « triangle fixe » tombe aussi, sans Behbahani–Lam.
- OBSERVÉ puis DÉRIVÉ (D10) : d_S = d_1·d_ω² exactement (T(6), T(9), T(12), 145 cas aléatoires) ; donc le réseau propre complet ne
  voit pas l'obstruction, seule la congruence entre caractères la voit.
- DÉRIVÉ : **preuve élémentaire** — les réductions de Z_3^33 ∩ V_3(Q) et Z_3[ω]^33 ∩ V_3(M) sont le même espace quadratique
  (F_3^33/rad, (Q+I) mod 3) car Q ≡ M (mod 1−ω) ; discriminant 2 d'un côté, 1 de l'autre. Vérifiée sur graphes réels.
- D2 : critère avec points fixes sur tous les srg faisables v ≤ 1300 : s'applique à 108 jeux ; exclut l'ordre 3 (β = 0) pour 9,
  tous d'existence inconnue chez Brouwer (dont 714, 722, 1148). `logs/criterion_scan2_1300.log`.
- D3 (C_p, p > 3) : la preuve élémentaire donne (d_1/p) = (d_ζ/p). Pour le graphe de Moore (p = 13, action libre), d_1 = 2·3^a·5^b
  et d_ζ est supporté sur les premiers au-dessus de 3 et 5 dans Q(ζ13)+ : les exposants inconnus laissent a priori de la liberté ;
  il faudrait des contraintes supplémentaires (5-rang de A+8I, etc.). PARI indisponible ici (cypari2 ne compile pas). SPÉCULATION.

## Rédaction et formalisation (2026-09-23, après-midi)
- `pdf/preuve_c3.pdf` (4 p., source `pdf/preuve_c3.tex`, compilé avec Tectonic dans `tools/`) : preuve élémentaire
  (théorème matriciel en 6 étapes), cas du triangle fixe, remarques, références.
- Lean 4 v4.35.0-rc2 + Mathlib (installés via elan ; projet `c3formal/`) :
  - **Étape 5 formalisée d'abord** (`C3formal/Step5.lean`, demande de l'utilisateur), puis tout le théorème central.
  - **`C3.no_pair` vérifié** (théorème 5 du PDF) : `#print axioms` → `[propext, Classical.choice, Quot.sound]`,
    aucun `sorry` (`logs/lean_axioms.log`).
  - Fichiers : Eis, EisEuclid (ℤ[ω] euclidien), EisComplex (positivité via ℂ), Saturated (étapes 2–3),
    Step5, NumberTheory, IntPart (étapes 1, 3, 4 côté ℤ), Main.
  - Non formalisés : lemme 4 (graphe → matrices, combinatoire classique) et proposition 2 (triangle fixe).
  - Statut : DÉRIVÉ + **VÉRIFIÉ PAR MACHINE** pour le théorème matriciel ; le passage graphe → matrices reste
    une démonstration papier (courte, classique) à relire.

## Formalisation complète du théorème 1 et de la proposition 2 (2026-09-23, soir)
- Lemme 4 (graphe → matrices) formalisé : `Bridge.lean` (`no_shift_invariant`) + `Graph.lean` (réétiquetage
  V ≃ Fin 33 × ZMod 3). **`C3.no_free_order3` (théorème 1) vérifié à partir de `SimpleGraph.IsSRGWith` (Mathlib).**
- Cas du triangle, nouvel argument **sans l'identité d'Ishida** (DÉRIVÉ) : les lignes fixes de Ñ = 11(Ã+4I) − 2·1wᵀ sont
  ≡ 0 (mod 3), donc les coordonnées fixes des 3-vecteurs propres invariants entiers sont divisibles par 3 ; le Gram pondéré
  G̃ = BᵀDB/3 est entier, G̃K = 77I avec K = C(ÑΔ)Cᵀ ; modulo 3 tout se passe dans le bloc 32 × 32, l'étape 5 s'applique
  telle quelle (r = r', det G̃ ≡ 1) ; la parité 11-adique avec 1ᵀD1 = 99 donne det G̃ ≡ 2. Contradiction.
- Lean : `TriangleMatrix`, `TriangleMain`, `TriangleStep5`, `TriangleStep4` (**`C3.Tri.no_triangle_pair`**),
  `TriangleBridge` (lemme 4 version triangle, via les matrices E, R, E_ω), `TriangleGraph`.
- Renforcement : « exactement 3 points fixes » suffit, le triangle est démontré (`fixed_adj` : sinon μ = 2 donne au moins
  4 points fixes). Avec `three_dvd_card_nonfixed` : **`C3.no_order3_fix_le3`** (aucun automorphisme d'ordre 3 ayant au plus
  3 points fixes).
- `#print axioms` des 5 énoncés (no_pair, no_free_order3, Tri.no_triangle_pair, no_triangle_order3, no_order3_fix_le3)
  → [propext, Classical.choice, Quot.sound] ; aucun `sorry` ; `lake build` complet OK (2243 tâches).
  `logs/lean_axioms_final.log`.
- Seule entrée non formalisée de la chaîne « aucun automorphisme d'ordre 3 » : Makhnev–Minakova (Fix vide ou triangle).
- PDF mis à jour : prop. 2 pour « exactement trois points fixes », §4 réécrit sans Ishida, remarques Lean ; plus de
  contrainte de 4 pages (demande de l'utilisateur) : 5 pages, marges 2,5 cm. Ancienne source : `pdf/preuve_c3_v1_ishida.tex`.
- Statuts : théorème 1 et proposition 2 : DÉRIVÉ + vérifiés par machine (Lean, depuis la définition Mathlib d'un srg).
  Corollaire 3 : conditionnel à Makhnev–Minakova (ÉTABLI dans la littérature, non vérifié ici). Aucune relecture humaine
  indépendante à ce jour.

## Makhnev–Minakova remplacé : chaîne complète vérifiée (2026-09-23, fin de soirée)
- Question de l'utilisateur : pourquoi Makhnev–Minakova reste hors de Lean. Réponse : il manquait seulement le lemme
  « un automorphisme d'ordre 3 a au plus 3 points fixes » (MM04 : Fix vide ou triangle), que je citais.
- Preuve élémentaire trouvée (DÉRIVÉ) : (1) un sommet adjacent à deux points fixes est fixe (λ = 1, μ = 2) ; (2) un point
  fixe a n ∈ {2, 8, 14} voisins fixes (≡ 14 mod 3 par les orbites, pair par l'appariement λ = 1) ; (3) un sommet non fixe
  a au plus un voisin fixe, d'où 15|F| ≤ 99 + Σ n ; (4) n = 14 ⇒ g = 1 ; n = 8 ⇒ 15(9+s) ≤ 123 + 10s, impossible ;
  tous n = 2 ⇒ |F| ≤ 3. Pas de valeurs propres (le cas srg(33,8,1,2) tombe par le comptage (3)).
- Lean : `C3formal/FixLemma.lean` ; **`C3.no_order3`** : tout automorphisme σ d'un srg(99,14,1,2) avec σ³ = 1 est
  l'identité. `#print axioms` → [propext, Classical.choice, Quot.sound] ; `lake build` complet OK (2244 tâches).
  `logs/lean_axioms_final.log`.
- PDF : nouveau §5 (lemme 7, points fixes), corollaire 3 démontré sans [MM04] (cité pour l'énoncé), remarques mises à
  jour ; 6 pages. Sauvegarde de la version précédente : `pdf/preuve_c3_v2_avant_lemme_fix.tex`.
- Statut : corollaire 3 (aucun automorphisme d'ordre 3) : DÉRIVÉ + vérifié par machine, sans entrée extérieure.
  Aucune relecture humaine indépendante à ce jour.
