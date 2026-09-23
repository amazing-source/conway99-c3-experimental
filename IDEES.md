# Registre des pistes (divergence du 2026-09-23)

Épuisé dans C3 (ÉTABLI, lu dans le dépôt) : tau = 6 (trace du module libre), 26 graphes F (Farkas), 46 classes de phases,
lemmes de type/triplets, énumérations de supports, étage quotient par SAT (aucune solution), condition spectrale sur C (négative),
modèle complet au niveau des sommets (indécis). **Jamais utilisé** : discriminants, réseaux propres, droites du quadrangle
partiel, rangs modulaires autres que la trace, arithmétique de Z[ω] au-delà de la définition de M.

Axes : potentiel (P : 1–5) · coût pour falsifier (C : 1 = minutes, 5 = jours).

| # | piste | nature | P | C | statut |
|---|---|---|---|---|---|
| D1 | **Discriminant hermitien du module libre E_3·Z_3^99** : congruence d_1 ≡ d_ω (mod 3) | module/réseau 3-adique | 5 | 1 | **DÉRIVÉ + OBSERVÉ → tue C3** (notes/P1) |
| D2 | Critère général p = 3 pour tout srg, avec points fixes (β = 0) | généralisation | 3 | 1 | DÉRIVÉ + OBSERVÉ : 9 exclusions (v ≤ 1300), toutes d'existence inconnue |
| D3 | Version C_p (p > 3) : symbole de Legendre de d_1 vs d_ζ sur Z[ζ_p] ; cibles : graphe de Moore (ordre 13), srg(352,26,0,2) (ordre 11), srg(1276,50,0,2) (11, 29) | transfert du mécanisme | 4 | 3 | SPÉCULATION : pour Moore p=13, exposants libres des deux côtés ; besoin du 5-rang de A+8I ; PARI absent |
| D4 | Q seul est-il impossible ? L'étage quotient est toujours UNSAT ; P1 a besoin de M. Chercher l'obstruction propre à Q | « petit théorème » derrière le solveur | 3 | 3 | CONJECTURE ouverte |
| D5 | Hypergraphe des orbites de droites (quotient du quadrangle partiel PQ(2,6,2)) : 75 blocs, holonomie plate, Q_XU+Q_XV+Q_XW ≤ 3 | changement de représentation | 2 | 2 | HEURISTIQUE (moins utile si D1 tient) |
| D6 | Invariants 7-adiques : 7 = θθ̄ décomposé, 3 ≡ −4 (mod 7) ; rang de M − 3I mod θ, lien avec le 7-rang de A − 3I | rang modulaire | 2 | 2 | IDÉE |
| D7 | Comptage de points fixes mod 3 de sous-structures déterminées par les paramètres (hexagones induits, etc.) | congruence combinatoire | 2 | 2 | IDÉE |
| D8 | Raffinements « d'ordre supérieur » du module libre : au-delà de rang et discriminant, invariant de Hasse / forme de Witt du module hermitien sur Z_3[C3] | K-théorie hermitienne | 3 | 4 | SPÉCULATION |
| D9 | Le phénomène pour lui-même : pour quels paramètres (v,k,λ,μ,p) le vecteur **1** crée-t-il une obstruction ? Loi de réciprocité cachée expliquant l'accord systématique pour T(n) ? | théorie | 3 | 2 | HEURISTIQUE |
| D10 | Relation globale d_S = d_1·d_ω² (observée sur l'exemple manuel ; à tester) et genre de Z[C3]-réseaux | réseaux globaux | 2 | 1 | OBSERVÉ + DÉRIVÉ : d_S = d_1·d_ω² exactement ; le réseau complet ne voit pas l'obstruction |
| D11 | Attaques contre D1 : chercher un graphe réel avec action libre d'ordre 3 exclu par le critère ; relâcher des hypothèses (β ≠ 0) pour voir ce qui casse | falsification | 5 | 2 | aucun contre-exemple ; preuve élémentaire trouvée en chemin (même espace quadratique sur F_3) |
| D12 | Structure des doubles (2-facteur D) : holonomie des cycles de D, lien avec les droites | combinatoire locale | 1 | 2 | IDÉE |

Choix : D1 (fait), D11 (en continu), D2 et D10 (peu coûteux), puis D3 (fort potentiel, coût moyen), puis D4.
