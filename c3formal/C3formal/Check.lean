import C3formal.FixLemma

-- Théorème 5 (théorème matriciel, cas sans point fixe)
#print axioms C3.no_pair
-- Théorème 1 (graphe, sans point fixe)
#print axioms C3.no_free_order3
#check @C3.no_free_order3
-- Proposition 2, forme matricielle (triangle fixe)
#print axioms C3.Tri.no_triangle_pair
-- Proposition 2 (graphe, exactement 3 points fixes ; le triangle est démontré, pas supposé)
#print axioms C3.no_triangle_order3
#check @C3.no_triangle_order3
-- Théorème 1 + proposition 2 : au plus 3 points fixes
#print axioms C3.no_order3_fix_le3
#check @C3.no_order3_fix_le3
-- Corollaire 3, sans entrée extérieure : tout automorphisme σ avec σ³ = 1 est l'identité
#print axioms C3.no_order3
#check @C3.no_order3
