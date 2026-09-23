import C3formal.TriangleGraph
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The fixed points of an automorphism of order 3, and the final theorem

This file replaces the external input (Makhnev–Minakova: the fixed points of an automorphism of
order 3 form the empty set or a triangle) by an elementary counting argument.

Let `σ` be an automorphism of an `srg(99,14,1,2)` with `σ³ = 1`, `F` its set of fixed points and,
for a vertex `y`, `nfix y` the number of fixed neighbours of `y`.

* `fixed_of_two_fixed` : a vertex adjacent to two fixed vertices is fixed (`λ = 1`, `μ = 2`);
* `nfix_mod3`, `nfix_even` : for `x ∈ F`, `nfix x ≡ 14 (mod 3)` (the other neighbours form orbits of
  size 3) and `nfix x` is even (`λ = 1` pairs the fixed neighbours); hence `nfix x ∈ {2, 8, 14}`;
* `key_ineq` : a non-fixed vertex has at most one fixed neighbour, so `15 |F| ≤ 99 + ∑_{y ∈ F} nfix y`;
* `all_fixed_of_nfix14` : `nfix x = 14` forces `σ = 1`;
* `no_nfix8` : `nfix x = 8` contradicts `key_ineq` (`111 ≤ 99`);
* `card_fixF_le3` : if `nfix = 2` on `F`, then `|F| ≤ 3`.

With `no_order3_fix_le3` (theorem 1 + proposition 2): **`no_order3`**, every automorphism `σ` with
`σ³ = 1` is the identity.
-/

open Finset

namespace C3

section fixlemma

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The fixed points of `σ`. -/
def fixF (σ : G ≃g G) : Finset V := univ.filter (fun v => σ v = v)

/-- The number of fixed neighbours of `y`. -/
def nfix (σ : G ≃g G) (y : V) : ℕ := (univ.filter (fun v => G.Adj y v ∧ σ v = v)).card

/-- The number of non-fixed neighbours of `y`. -/
def nnon (σ : G ≃g G) (y : V) : ℕ := (univ.filter (fun v => G.Adj y v ∧ ¬ σ v = v)).card

theorem mem_fixF {σ : G ≃g G} {v : V} : v ∈ fixF σ ↔ σ v = v := by
  simp [fixF]

/-- A set of common neighbours of `x` and `y` has at most `|G.commonNeighbors x y|` elements. -/
theorem card_le_common (s : Finset V) (x y : V) (h : ∀ w ∈ s, G.Adj x w ∧ G.Adj y w) :
    s.card ≤ Fintype.card (G.commonNeighbors x y) := by
  rw [← Set.toFinset_card]
  apply Finset.card_le_card
  intro w hw
  rw [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  exact h w hw

/-- A vertex adjacent to two distinct fixed vertices is fixed. -/
theorem fixed_of_two_fixed (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) {a b v : V} (ha : σ a = a) (hb : σ b = b) (hab : a ≠ b)
    (hav : G.Adj a v) (hbv : G.Adj b v) : σ v = v := by
  by_cases hadj : G.Adj a b
  · have hcard := hG.of_adj a b hadj
    have hσa : G.Adj a (σ v) := by
      have h := σ.map_adj_iff (v := a) (w := v)
      rw [ha] at h
      exact h.mpr hav
    have hσb : G.Adj b (σ v) := by
      have h := σ.map_adj_iff (v := b) (w := v)
      rw [hb] at h
      exact h.mpr hbv
    have h1 := Fintype.card_le_one_iff.mp (le_of_eq hcard)
      ⟨σ v, (G.mem_commonNeighbors).mpr ⟨hσa, hσb⟩⟩ ⟨v, (G.mem_commonNeighbors).mpr ⟨hav, hbv⟩⟩
    exact congrArg Subtype.val h1
  · exact common_nbr_fixed hG σ h3 ha hb hab hadj hav hbv

theorem nfix_add_nnon (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (x : V) :
    nfix σ x + nnon σ x = 14 := by
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset x) (fun v => σ v = v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hG.regular x, SimpleGraph.neighborFinset_eq_filter,
    Finset.filter_filter, Finset.filter_filter] at h
  exact h

/-- `nfix x ≡ 14 (mod 3)`: the non-fixed neighbours of a fixed vertex form orbits of size 3. -/
theorem nfix_mod3 (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v)
    {x : V} (hx : σ x = x) : nfix σ x % 3 = 2 := by
  have hmem : ∀ v, G.Adj x v ↔ G.Adj x (σ v) := by
    intro v
    have h := σ.map_adj_iff (v := x) (w := v)
    rw [hx] at h
    exact h.symm
  let τ : {v // G.Adj x v} ≃ {v // G.Adj x v} :=
    Equiv.subtypeEquiv (p := fun v => G.Adj x v) (q := fun v => G.Adj x v) σ.toEquiv hmem
  have hτ : ∀ w, τ (τ (τ w)) = w := fun w => Subtype.ext (by simp [τ, h3])
  have hdvd := three_dvd_card_nonfixed τ hτ
  have hcard : Fintype.card {w : {v // G.Adj x v} // ¬ τ w = w} = nnon σ x := by
    unfold nnon
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun w => ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => G.Adj x v) (fun v => ¬ σ v = v)))
    simp [τ, Subtype.ext_iff]
  have hsum := nfix_add_nnon hG σ x
  rw [hcard] at hdvd
  omega

/-- `nfix x` is even: `λ = 1` pairs each fixed neighbour of `x` with the common neighbour of the two,
which is again a fixed neighbour of `x`. -/
theorem nfix_even (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v)
    {x : V} (hx : σ x = x) : Even (nfix σ x) := by
  have hex : ∀ u : {v // G.Adj x v ∧ σ v = v}, ∃ w : {v // G.Adj x v ∧ σ v = v},
      G.Adj u.1 w.1 := by
    intro u
    have hc := hG.of_adj x u.1 u.2.1
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors x u.1))
    have hcm := (G.mem_commonNeighbors).mp c.2
    have hfc : σ c = c := fixed_of_two_fixed hG σ h3 hx u.2.2 (G.ne_of_adj u.2.1) hcm.1 hcm.2
    exact ⟨⟨c.1, hcm.1, hfc⟩, hcm.2⟩
  have huniq : ∀ u w w' : {v // G.Adj x v ∧ σ v = v}, G.Adj u.1 w.1 → G.Adj u.1 w'.1 → w = w' := by
    intro u w w' hw hw'
    have hc := hG.of_adj x u.1 u.2.1
    have h1 := Fintype.card_le_one_iff.mp (le_of_eq hc)
      ⟨w.1, (G.mem_commonNeighbors).mpr ⟨w.2.1, hw⟩⟩ ⟨w'.1, (G.mem_commonNeighbors).mpr ⟨w'.2.1, hw'⟩⟩
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  choose f hf using hex
  have hinv : Function.Involutive f := fun u => huniq (f u) (f (f u)) u (hf (f u)) (hf u).symm
  have hfree : ∀ u, f u ≠ u := by
    intro u h
    have h' := hf u
    rw [h] at h'
    exact G.ne_of_adj h' rfl
  have hπ2 : (hinv.toPerm f) ^ 2 = 1 := by
    ext u
    simp [sq, hinv u]
  have hsupp : (hinv.toPerm f).support = univ := by
    apply Finset.eq_univ_of_forall
    intro u
    rw [Equiv.Perm.mem_support]
    exact hfree u
  have h2 := Equiv.Perm.two_dvd_card_support hπ2
  rw [hsupp, Finset.card_univ, Fintype.card_subtype] at h2
  exact even_iff_two_dvd.mpr h2

/-- A non-fixed vertex has at most one fixed neighbour; counting the edges between `F` and its
complement gives `15 |F| ≤ 99 + ∑_{y ∈ F} nfix y`. -/
theorem key_ineq (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v) :
    15 * (fixF σ).card ≤ 99 + ∑ y ∈ fixF σ, nfix σ y := by
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := fixF σ) (t := univ.filter (fun v => ¬ σ v = v)) (fun y v => G.Adj y v)
  have e1 : ∀ y, ((univ.filter (fun v => ¬ σ v = v)).bipartiteAbove (fun y v => G.Adj y v) y).card =
      nnon σ y := by
    intro y
    unfold nnon
    congr 1
    ext v
    simp only [Finset.mem_bipartiteAbove, mem_filter, mem_univ, true_and]
    exact and_comm
  have e2 : ∀ v ∈ univ.filter (fun v => ¬ σ v = v),
      ((fixF σ).bipartiteBelow (fun y v => G.Adj y v) v).card ≤ 1 := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_bipartiteBelow, mem_fixF] at ha hb
    by_contra hab
    exact hv (fixed_of_two_fixed hG σ h3 ha.1 hb.1 hab ha.2 hb.2)
  have hnn : ∑ y ∈ fixF σ, nnon σ y ≤ (univ.filter (fun v => ¬ σ v = v)).card := by
    calc ∑ y ∈ fixF σ, nnon σ y
        = ∑ v ∈ univ.filter (fun v => ¬ σ v = v),
            ((fixF σ).bipartiteBelow (fun y v => G.Adj y v) v).card := by
          rw [← hdc]
          exact Finset.sum_congr rfl fun y _ => (e1 y).symm
      _ ≤ ∑ v ∈ univ.filter (fun v => ¬ σ v = v), 1 := Finset.sum_le_sum e2
      _ = (univ.filter (fun v => ¬ σ v = v)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hcard : (fixF σ).card + (univ.filter (fun v => ¬ σ v = v)).card = 99 := by
    unfold fixF
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, hG.card]
  have hsum : ∑ y ∈ fixF σ, (nfix σ y + nnon σ y) = 14 * (fixF σ).card := by
    rw [Finset.sum_congr rfl fun y _ => nfix_add_nnon hG σ y, Finset.sum_const, smul_eq_mul,
      mul_comm]
  rw [Finset.sum_add_distrib] at hsum
  omega

/-- If a fixed vertex has all its 14 neighbours fixed, every vertex is fixed (diameter 2). -/
theorem all_fixed_of_nfix14 (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) {x : V} (hx : σ x = x) (h14 : nfix σ x = 14) : ∀ v, σ v = v := by
  have hn := nfix_add_nnon hG σ x
  have h0 : nnon σ x = 0 := by omega
  have hnb : ∀ v, G.Adj x v → σ v = v := by
    intro v hv
    by_contra hne
    have hmem : v ∈ univ.filter (fun v => G.Adj x v ∧ ¬ σ v = v) := by simp [hv, hne]
    unfold nnon at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact Finset.notMem_empty v hmem
  intro v
  by_cases hvx : v = x
  · rw [hvx]
    exact hx
  by_cases hadj : G.Adj x v
  · exact hnb v hadj
  have hcard := hG.of_not_adj (fun h => hvx h.symm) hadj
  obtain ⟨a, b, hab⟩ :=
    Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card (G.commonNeighbors x v))
  have ha := (G.mem_commonNeighbors).mp a.2
  have hb := (G.mem_commonNeighbors).mp b.2
  exact fixed_of_two_fixed hG σ h3 (hnb _ ha.1) (hnb _ hb.1) (fun h => hab (Subtype.ext h))
    ha.2.symm hb.2.symm

/-- A fixed vertex cannot have 8 fixed neighbours when no fixed vertex has 14. -/
theorem no_nfix8 (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v)
    {x : V} (hx : σ x = x) (h8 : 8 ≤ nfix σ x) (hle : ∀ y, σ y = y → nfix σ y ≤ 8) : False := by
  have hkey := key_ineq hG σ h3
  obtain ⟨A, hA⟩ : ∃ A : Finset V, A = univ.filter (fun v => G.Adj x v ∧ σ v = v) := ⟨_, rfl⟩
  have hAcard : A.card = nfix σ x := by rw [hA]; rfl
  have hmemA : ∀ v, v ∈ A ↔ G.Adj x v ∧ σ v = v := by
    intro v
    rw [hA]
    simp
  obtain ⟨S, hS⟩ : ∃ S : Finset V, S = fixF σ \ insert x A := ⟨_, rfl⟩
  have hxA : x ∉ A := by
    rw [hmemA]
    exact fun h => G.ne_of_adj h.1 rfl
  have hsubF : insert x A ⊆ fixF σ := by
    intro v hv
    rw [mem_insert] at hv
    rw [mem_fixF]
    rcases hv with rfl | hv
    · exact hx
    · exact ((hmemA v).mp hv).2
  have hFeq : fixF σ = insert x A ∪ S := by
    rw [hS]
    exact (Finset.union_sdiff_of_subset hsubF).symm
  have hdisj : Disjoint (insert x A) S := by
    rw [hS]
    exact Finset.disjoint_sdiff
  have hFcard : (fixF σ).card = A.card + 1 + S.card := by
    rw [hFeq, Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hxA]
  have hsum : ∑ y ∈ fixF σ, nfix σ y = nfix σ x + ∑ u ∈ A, nfix σ u + ∑ y ∈ S, nfix σ y := by
    rw [hFeq, Finset.sum_union hdisj, Finset.sum_insert hxA]
  have hmemS : ∀ y ∈ S, σ y = y ∧ y ≠ x ∧ ¬ G.Adj x y := by
    intro y hy
    rw [hS, mem_sdiff, mem_insert, mem_fixF] at hy
    exact ⟨hy.1, fun h => hy.2 (Or.inl h), fun h => hy.2 (Or.inr ((hmemA y).mpr ⟨h, hy.1⟩))⟩
  -- a fixed neighbour `u` of `x`: its fixed neighbours are `x`, at most one vertex of `A`, and
  -- vertices of `S`
  have hAb : ∀ u ∈ A, nfix σ u ≤ 2 + (S.filter (fun y => G.Adj u y)).card := by
    intro u hu
    have hu' := (hmemA u).mp hu
    have hsub : univ.filter (fun v => G.Adj u v ∧ σ v = v) ⊆
        ({x} ∪ A.filter (fun w => G.Adj u w)) ∪ S.filter (fun y => G.Adj u y) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      have hvF : v ∈ fixF σ := mem_fixF.mpr hv.2
      rw [hFeq, mem_union, mem_insert] at hvF
      simp only [mem_union, mem_singleton, mem_filter]
      rcases hvF with (hvx | hvA) | hvS
      · exact Or.inl (Or.inl hvx)
      · exact Or.inl (Or.inr ⟨hvA, hv.1⟩)
      · exact Or.inr ⟨hvS, hv.1⟩
    have hA1 : (A.filter (fun w => G.Adj u w)).card ≤ 1 := by
      have h := card_le_common (A.filter (fun w => G.Adj u w)) x u (fun w hw => by
        rw [mem_filter] at hw
        exact ⟨((hmemA w).mp hw.1).1, hw.2⟩)
      rwa [hG.of_adj x u hu'.1] at h
    calc nfix σ u = (univ.filter (fun v => G.Adj u v ∧ σ v = v)).card := rfl
      _ ≤ (({x} ∪ A.filter (fun w => G.Adj u w)) ∪ S.filter (fun y => G.Adj u y)).card :=
          Finset.card_le_card hsub
      _ ≤ ({x} ∪ A.filter (fun w => G.Adj u w)).card + (S.filter (fun y => G.Adj u y)).card :=
          Finset.card_union_le _ _
      _ ≤ (({x} : Finset V).card + (A.filter (fun w => G.Adj u w)).card) +
            (S.filter (fun y => G.Adj u y)).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 2 + (S.filter (fun y => G.Adj u y)).card := by
          rw [Finset.card_singleton]
          omega
  -- a vertex of `S` has at most `μ = 2` neighbours in `A`
  have hSb : ∀ y ∈ S, (A.filter (fun u => G.Adj u y)).card ≤ 2 := by
    intro y hy
    obtain ⟨-, hyx, hxy⟩ := hmemS y hy
    have h := card_le_common (A.filter (fun u => G.Adj u y)) x y (fun w hw => by
      rw [mem_filter] at hw
      exact ⟨((hmemA w).mp hw.1).1, hw.2.symm⟩)
    rwa [hG.of_not_adj (fun h => hyx h.symm) hxy] at h
  have hdc : ∑ u ∈ A, (S.filter (fun y => G.Adj u y)).card =
      ∑ y ∈ S, (A.filter (fun u => G.Adj u y)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun u y => G.Adj u y)
  have hA_sum : ∑ u ∈ A, nfix σ u ≤ 2 * A.card + 2 * S.card := by
    calc ∑ u ∈ A, nfix σ u ≤ ∑ u ∈ A, (2 + (S.filter (fun y => G.Adj u y)).card) :=
          Finset.sum_le_sum hAb
      _ = 2 * A.card + ∑ u ∈ A, (S.filter (fun y => G.Adj u y)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * A.card + ∑ y ∈ S, 2 := by
          rw [hdc]
          exact Nat.add_le_add_left (Finset.sum_le_sum hSb) _
      _ = 2 * A.card + 2 * S.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  have hS_sum : ∑ y ∈ S, nfix σ y ≤ 8 * S.card := by
    calc ∑ y ∈ S, nfix σ y ≤ ∑ y ∈ S, 8 :=
          Finset.sum_le_sum fun y hy => hle y (hmemS y hy).1
      _ = 8 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- If every fixed vertex has exactly 2 fixed neighbours, there are at most 3 fixed vertices. -/
theorem card_fixF_le3 (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v)
    {x : V} (hx : σ x = x) (h2 : ∀ y, σ y = y → nfix σ y ≤ 2) : (fixF σ).card ≤ 3 := by
  have hsub : fixF σ ⊆ insert x (univ.filter (fun v => G.Adj x v ∧ σ v = v)) := by
    intro y hy
    rw [mem_fixF] at hy
    simp only [mem_insert, mem_filter, mem_univ, true_and]
    by_cases hyx : y = x
    · exact Or.inl hyx
    refine Or.inr ⟨?_, hy⟩
    by_contra hxy
    -- `y` is fixed, not adjacent to `x`: take a common neighbour `a` of `x` and `y` (fixed), and the
    -- common neighbour `c` of `x` and `a` (fixed); then `a` has the 3 fixed neighbours `x, y, c`
    have hcard := hG.of_not_adj (fun h => hyx h.symm) hxy
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors x y))
    have ha := (G.mem_commonNeighbors).mp a.2
    have hfa : σ a = a := fixed_of_two_fixed hG σ h3 hx hy (fun h => hyx h.symm) ha.1 ha.2
    have hc1 := hG.of_adj x a ha.1
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors x a))
    have hc := (G.mem_commonNeighbors).mp c.2
    have hfc : σ c = c := fixed_of_two_fixed hG σ h3 hx hfa (G.ne_of_adj ha.1) hc.1 hc.2
    have hsub3 : ({x, y, c.1} : Finset V) ⊆ univ.filter (fun v => G.Adj a v ∧ σ v = v) := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      simp only [mem_filter, mem_univ, true_and]
      rcases hv with rfl | rfl | rfl
      · exact ⟨ha.1.symm, hx⟩
      · exact ⟨ha.2.symm, hy⟩
      · exact ⟨hc.2, hfc⟩
    have hxy' : x ≠ y := fun h => hyx h.symm
    have hxc : x ≠ c.1 := G.ne_of_adj hc.1
    have hyc : y ≠ c.1 := fun h => hxy (h ▸ hc.1)
    have hcard3 : ({x, y, c.1} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hyc]
      simp [hxy', hxc]
    have hle3 := Finset.card_le_card hsub3
    have h2a := h2 a hfa
    unfold nfix at h2a
    omega
  have h2x := h2 x hx
  unfold nfix at h2x
  calc (fixF σ).card ≤ (insert x (univ.filter (fun v => G.Adj x v ∧ σ v = v))).card :=
        Finset.card_le_card hsub
    _ ≤ (univ.filter (fun v => G.Adj x v ∧ σ v = v)).card + 1 := Finset.card_insert_le _ _
    _ ≤ 3 := by omega

end fixlemma

/-- **Corollary 3, without external input.** Every automorphism `σ` of a strongly regular graph with
parameters `(99, 14, 1, 2)` such that `σ³ = 1` is the identity: the graph has no automorphism of
order 3. -/
theorem no_order3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) : ∀ v, σ v = v := by
  by_contra hne
  push_neg at hne
  obtain ⟨v0, hv0⟩ := hne
  apply no_order3_fix_le3 G hG σ h3
  rw [Fintype.card_subtype]
  change (fixF σ).card ≤ 3
  have hval : ∀ y, σ y = y → nfix σ y = 2 ∨ nfix σ y = 8 ∨ nfix σ y = 14 := by
    intro y hy
    have hm := nfix_mod3 hG σ h3 hy
    have he := nfix_even hG σ h3 hy
    have hs := nfix_add_nnon hG σ y
    rw [Nat.even_iff] at he
    omega
  by_cases h14 : ∃ y, σ y = y ∧ nfix σ y = 14
  · obtain ⟨y, hy, hy14⟩ := h14
    exact absurd (all_fixed_of_nfix14 hG σ h3 hy hy14 v0) hv0
  push_neg at h14
  by_cases h8 : ∃ y, σ y = y ∧ nfix σ y = 8
  · obtain ⟨y, hy, hy8⟩ := h8
    refine (no_nfix8 hG σ h3 hy (by omega) fun z hz => ?_).elim
    rcases hval z hz with h | h | h
    · omega
    · omega
    · exact absurd h (h14 z hz)
  push_neg at h8
  by_cases hF : ∃ x, σ x = x
  · obtain ⟨x, hx⟩ := hF
    refine card_fixF_le3 hG σ h3 hx fun y hy => ?_
    rcases hval y hy with h | h | h
    · omega
    · exact absurd h (h8 y hy)
    · exact absurd h (h14 y hy)
  · push_neg at hF
    have hempty : fixF σ = ∅ := by
      ext v
      simp [fixF, hF v]
    rw [hempty, Finset.card_empty]
    omega

end C3
