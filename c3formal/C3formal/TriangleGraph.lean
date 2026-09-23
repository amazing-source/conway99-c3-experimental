import C3formal.TriangleBridge
import C3formal.Graph

/-!
# Proposition 2 (graph form) and the combined statement

* `exists_relabel_free` : a fixed-point-free permutation of order 3 is a shift on `Fin m × ZMod 3`;
* `exists_relabel_tri` : a permutation of order 3 of a 99-set with exactly 3 fixed points is, after
  relabelling by `(Fin 32 × ZMod 3) ⊕ Fin 3`, the shift on the first summand and the identity on the
  second;
* `fixed_adj` : in an `srg(99,14,1,2)`, if an automorphism of order 3 has exactly 3 fixed points,
  they are pairwise adjacent (common neighbours of two fixed points are fixed; `μ = 2` would give a
  4th and a 5th fixed point);
* `no_triangle_order3` : no automorphism of order 3 with exactly 3 fixed points (Proposition 2);
* `no_order3_fix_le3` : no automorphism of order 3 with at most 3 fixed points (Theorem 1 +
  Proposition 2; the number of fixed points is `≡ 99 ≡ 0 (mod 3)`).
-/

open Matrix

namespace C3

section relabel_gen

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_relabel_free (σ : V ≃ V) (h3 : ∀ v, σ (σ (σ v)) = v) (hfree : ∀ v, σ v ≠ v) :
    ∃ m : ℕ, ∃ e : Fin m × ZMod 3 ≃ V, ∀ U b, e (U, b + 1) = σ (e (U, b)) := by
  classical
  let S := orbitSetoid h3
  let O := Quotient S
  let φ : O × ZMod 3 → V := fun p => sp σ p.2 p.1.out
  have hinj : Function.Injective φ := by
    rintro ⟨o, b⟩ ⟨o', b'⟩ h
    simp only [φ] at h
    have hoo : o = o' := by
      rw [← Quotient.out_eq o, ← Quotient.out_eq o']
      apply Quotient.sound
      refine ⟨-b' + b, ?_⟩
      rw [sp_add h3, h, ← sp_add h3, neg_add_cancel, sp_zero]
    subst hoo
    have : sp σ (b - b') (sp σ b' o.out) = sp σ b' o.out := by
      rw [← sp_add h3, sub_add_cancel, h]
    have hk := sp_eq_self h3 hfree this
    simp only [Prod.mk.injEq, true_and]
    exact (sub_eq_zero.mp hk)
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨k, hk⟩ : S (Quotient.mk S v).out v := Quotient.mk_out (s := S) v
    exact ⟨(Quotient.mk S v, k), hk.symm⟩
  let E : O × ZMod 3 ≃ V := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  let F : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  refine ⟨Fintype.card O, (Equiv.prodCongr F (Equiv.refl _)).trans E, ?_⟩
  intro U b
  change sp σ (b + 1) (F U).out = σ (sp σ b (F U).out)
  rw [add_comm, sp_add h3, sp_one]

/-- `σ` preserves the set of its non-fixed points. -/
theorem not_fixed_iff (σ : V ≃ V) (v : V) : ¬ σ v = v ↔ ¬ σ (σ v) = σ v :=
  not_congr σ.injective.eq_iff.symm

/-- The restriction of `σ` to its non-fixed points. -/
def σfree (σ : V ≃ V) : {v // ¬ σ v = v} ≃ {v // ¬ σ v = v} :=
  Equiv.subtypeEquiv (p := fun v => ¬ σ v = v) (q := fun v => ¬ σ v = v) σ (not_fixed_iff σ)

theorem σfree_apply (σ : V ≃ V) (v : {v // ¬ σ v = v}) : (σfree σ v).1 = σ v.1 := rfl

theorem exists_relabel_nonfixed (σ : V ≃ V) (h3 : ∀ v, σ (σ (σ v)) = v) :
    ∃ m : ℕ, ∃ e : Fin m × ZMod 3 ≃ {v // ¬ σ v = v},
      ∀ U b, e (U, b + 1) = σfree σ (e (U, b)) := by
  refine exists_relabel_free (σfree σ) (fun v => Subtype.ext ?_) (fun v h => v.2 ?_)
  · simp only [σfree_apply]
    exact h3 v.1
  · have := congrArg Subtype.val h
    simpa only [σfree_apply] using this

/-- The number of non-fixed points of an automorphism of order 3 is divisible by 3. -/
theorem three_dvd_card_nonfixed (σ : V ≃ V) (h3 : ∀ v, σ (σ (σ v)) = v) :
    3 ∣ Fintype.card {v // ¬ σ v = v} := by
  obtain ⟨m, e, -⟩ := exists_relabel_nonfixed σ h3
  have h := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] at h
  exact ⟨m, by rw [← h, mul_comm]⟩

theorem exists_relabel_tri (σ : V ≃ V) (hV : Fintype.card V = 99) (h3 : ∀ v, σ (σ (σ v)) = v)
    (hfix : Fintype.card {v // σ v = v} = 3) :
    ∃ e : (Fin 32 × ZMod 3) ⊕ Fin 3 ≃ V,
      (∀ U b, e (Sum.inl (U, b + 1)) = σ (e (Sum.inl (U, b)))) ∧
      (∀ t, σ (e (Sum.inr t)) = e (Sum.inr t)) := by
  obtain ⟨m, e1, he1⟩ := exists_relabel_nonfixed σ h3
  have hcard : Fintype.card {v // ¬ σ v = v} = Fintype.card V - Fintype.card {v // σ v = v} :=
    Fintype.card_subtype_compl _
  have hm : m * 3 = 96 := by
    have h := Fintype.card_congr e1
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] at h
    rw [hV, hfix] at hcard
    omega
  obtain rfl : m = 32 := by omega
  let e2 : Fin 3 ≃ {v // σ v = v} := (Fintype.equivFinOfCardEq hfix).symm
  refine ⟨(Equiv.sumCongr e1 e2).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun v => σ v = v))), ?_, ?_⟩
  · intro U b
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumComm_apply,
      Sum.swap_inl, Equiv.sumCompl_apply_inr, he1, σfree_apply]
  · intro t
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumComm_apply,
      Sum.swap_inr, Equiv.sumCompl_apply_inl]
    exact (e2 t).2

end relabel_gen

section graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A common neighbour of two fixed points of an automorphism of order 3 of an `srg(·,·,·,2)` is
fixed: the automorphism permutes the (at most two) common neighbours. -/
theorem common_nbr_fixed {n k ℓ : ℕ} (hG : G.IsSRGWith n k ℓ 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) {u v : V} (hu : σ u = u) (hv : σ v = v) (huv : u ≠ v)
    (hnadj : ¬ G.Adj u v) {w : V} (huw : G.Adj u w) (hvw : G.Adj v w) : σ w = w := by
  have hmem : ∀ x, G.Adj u x → G.Adj v x → G.Adj u (σ x) ∧ G.Adj v (σ x) := by
    intro x hux hvx
    constructor
    · have h := σ.map_adj_iff (v := u) (w := x)
      rw [hu] at h
      exact h.mpr hux
    · have h := σ.map_adj_iff (v := v) (w := x)
      rw [hv] at h
      exact h.mpr hvx
  obtain ⟨h1u, h1v⟩ := hmem w huw hvw
  obtain ⟨h2u, h2v⟩ := hmem (σ w) h1u h1v
  by_contra hw
  have hd2 : σ (σ w) ≠ σ w := fun h => hw (σ.injective h)
  have hd3 : σ (σ w) ≠ w := fun h => by
    apply hw
    have h' := congrArg σ h
    rw [h3] at h'
    exact h'.symm
  have hcard := hG.of_not_adj huv hnadj
  have h3lt : 2 < Fintype.card (G.commonNeighbors u v) := by
    rw [Fintype.two_lt_card_iff]
    refine ⟨⟨w, (G.mem_commonNeighbors).mpr ⟨huw, hvw⟩⟩,
      ⟨σ w, (G.mem_commonNeighbors).mpr ⟨h1u, h1v⟩⟩,
      ⟨σ (σ w), (G.mem_commonNeighbors).mpr ⟨h2u, h2v⟩⟩, ?_, ?_, ?_⟩
    · intro h
      exact hw (congrArg Subtype.val h).symm
    · intro h
      exact hd3 (congrArg Subtype.val h).symm
    · intro h
      exact hd2 (congrArg Subtype.val h).symm
  omega

/-- If an automorphism of order 3 of an `srg(99,14,1,2)` has exactly 3 fixed points, they form a
triangle. -/
theorem fixed_adj (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v)
    (hfix : Fintype.card {v // σ v = v} = 3) (u v : V) (hu : σ u = u) (hv : σ v = v)
    (huv : u ≠ v) : G.Adj u v := by
  by_contra hnadj
  have hcard := hG.of_not_adj huv hnadj
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card (G.commonNeighbors u v))
  have hx := (G.mem_commonNeighbors).mp x.2
  have hy := (G.mem_commonNeighbors).mp y.2
  have hfx := common_nbr_fixed hG σ h3 hu hv huv hnadj hx.1 hx.2
  have hfy := common_nbr_fixed hG σ h3 hu hv huv hnadj hy.1 hy.2
  have hux : u ≠ x.1 := G.ne_of_adj hx.1
  have huy : u ≠ y.1 := G.ne_of_adj hy.1
  have hvx : v ≠ x.1 := G.ne_of_adj hx.2
  have hvy : v ≠ y.1 := G.ne_of_adj hy.2
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have h4 : 4 ≤ Fintype.card {z // σ z = z} := by
    rw [Fintype.card_subtype]
    have hsub : ({u, v, x.1, y.1} : Finset V) ⊆ Finset.univ.filter (fun z => σ z = z) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hz with rfl | rfl | rfl | rfl
      · exact hu
      · exact hv
      · exact hfx
      · exact hfy
    have hc : ({u, v, x.1, y.1} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hxy']
      · simp [hvx, hvy]
      · simp [huv, hux, huy]
    calc 4 = ({u, v, x.1, y.1} : Finset V).card := hc.symm
      _ ≤ _ := Finset.card_le_card hsub
  omega

end graph

/-- **Proposition 2.** A strongly regular graph with parameters `(99, 14, 1, 2)` has no automorphism
of order 3 with exactly 3 fixed points (these would form a triangle). -/
theorem no_triangle_order3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) (hfix : Fintype.card {v // σ v = v} = 3) : False := by
  obtain ⟨e, he1, he2⟩ := exists_relabel_tri σ.toEquiv hG.card h3 hfix
  have he1' : ∀ U b, e (Sum.inl (U, b + 1)) = σ (e (Sum.inl (U, b))) := he1
  have he2' : ∀ t, σ (e (Sum.inr t)) = e (Sum.inr t) := he2
  have hadj := fixed_adj hG σ h3 hfix
  set A : Matrix V V ℤ := G.adjMatrix ℤ with hA
  have hAA : A * A + A = (12 : ℤ) • (1 : Matrix V V ℤ) + (2 : ℤ) • Matrix.of (fun _ _ => 1) := by
    have h := hG.matrix_eq (α := ℤ)
    rw [sq] at h
    ext v w
    have hvw := congrFun (congrFun h v) w
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.smul_apply] at hvw
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply,
      hvw]
    simp only [Matrix.one_apply, hA, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
      smul_eq_mul, nsmul_eq_mul]
    by_cases hvw' : v = w
    · subst hvw'
      simp
    · by_cases hadj : G.Adj v w <;> simp [hvw', hadj]
  apply Tri.no_tri_shift_invariant (A.submatrix e e)
  · rw [transpose_submatrix, hA, SimpleGraph.transpose_adjMatrix]
  · ext x
    rw [submatrix_mulVec_equiv]
    have hc : ((fun _ => (1 : ℤ)) ∘ e.symm) = Function.const V (1 : ℤ) := rfl
    rw [Function.comp_apply, hc, hA,
      SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hG.regular]
    norm_num
  · have hsub : (A.submatrix e e) * (A.submatrix e e) + A.submatrix e e
        = (A * A + A).submatrix e e := by
      rw [submatrix_mul_equiv]
      ext x y
      simp
    rw [hsub, hAA]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, e.injective.eq_iff]
  · intro U V' b c
    simp only [submatrix_apply, he1', hA, SimpleGraph.adjMatrix_apply]
    have key : G.Adj (σ (e (Sum.inl (U, b)))) (σ (e (Sum.inl (V', c)))) ↔
        G.Adj (e (Sum.inl (U, b))) (e (Sum.inl (V', c))) := σ.map_adj_iff
    simp only [key]
  · intro U b t
    simp only [submatrix_apply, he1', hA, SimpleGraph.adjMatrix_apply]
    have key : G.Adj (σ (e (Sum.inl (U, b)))) (e (Sum.inr t)) ↔
        G.Adj (e (Sum.inl (U, b))) (e (Sum.inr t)) := by
      have h := σ.map_adj_iff (v := e (Sum.inl (U, b))) (w := e (Sum.inr t))
      rw [he2' t] at h
      exact h
    simp only [key]
  · intro s t
    simp only [submatrix_apply, hA, SimpleGraph.adjMatrix_apply]
    by_cases hst : s = t
    · subst hst
      simp
    · have hne : e (Sum.inr s) ≠ e (Sum.inr t) :=
        fun h => hst (Sum.inr_injective (e.injective h))
      simp [hst, hadj _ _ (he2' s) (he2' t) hne]

/-- **Theorem 1 + Proposition 2.** A strongly regular graph with parameters `(99, 14, 1, 2)` has no
automorphism of order 3 with at most 3 fixed points. (By Makhnev–Minakova, the fixed points of an
automorphism of order 3 form the empty set or a triangle, so this excludes every automorphism of
order 3; that external input is not formalised.) -/
theorem no_order3_fix_le3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) (hfix : Fintype.card {v // σ v = v} ≤ 3) : False := by
  have hdvd : 3 ∣ Fintype.card {v // ¬ σ v = v} := three_dvd_card_nonfixed σ.toEquiv h3
  have hcard : Fintype.card {v // ¬ σ v = v} = Fintype.card V - Fintype.card {v // σ v = v} :=
    Fintype.card_subtype_compl _
  rw [hG.card] at hcard
  have hcases : Fintype.card {v // σ v = v} = 0 ∨ Fintype.card {v // σ v = v} = 3 := by omega
  rcases hcases with h0 | h3'
  · apply no_free_order3 G hG σ h3
    intro v hv
    rw [Fintype.card_eq_zero_iff] at h0
    exact h0.elim ⟨v, hv⟩
  · exact no_triangle_order3 G hG σ h3 h3'

end C3
