import C3formal.Bridge
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.Quotient

/-!
# Theorem 1: no `srg(99,14,1,2)` has a fixed-point-free automorphism of order 3

* `exists_relabel` : a fixed-point-free permutation `σ` of order 3 of a set with 99 elements is,
  after relabelling the set by `Fin 33 × ZMod 3`, the shift `(U, b) ↦ (U, b + 1)`;
* `no_free_order3` : the graph statement, deduced from `no_shift_invariant` (Lemma 4 + the matrix
  theorem `no_pair`).
-/

open Matrix

namespace C3

section relabel

variable {V : Type*} [Fintype V] [DecidableEq V] (σ : V ≃ V)

/-- `σ ^ k` for `k : ZMod 3`. -/
def sp (k : ZMod 3) (v : V) : V := σ^[k.val] v

variable {σ}

theorem iter_mod (h3 : ∀ v, σ (σ (σ v)) = v) (n : ℕ) (v : V) : σ^[n % 3] v = σ^[n] v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [show (m + 3) % 3 = m % 3 by omega, ih m (by omega), Function.iterate_add_apply]
      congr 1
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      exact (h3 v).symm

theorem sp_add (h3 : ∀ v, σ (σ (σ v)) = v) (a b : ZMod 3) (v : V) :
    sp σ (a + b) v = sp σ a (sp σ b v) := by
  simp only [sp]
  rw [ZMod.val_add, iter_mod h3, Function.iterate_add_apply]

theorem sp_zero (v : V) : sp σ 0 v = v := by simp [sp]

theorem sp_one (v : V) : sp σ 1 v = σ v := by
  simp [sp, ZMod.val_one]

theorem sp_eq_self (h3 : ∀ v, σ (σ (σ v)) = v) (hfree : ∀ v, σ v ≠ v) {k : ZMod 3} {v : V}
    (h : sp σ k v = v) : k = 0 := by
  have hk : k.val < 3 := ZMod.val_lt k
  unfold sp at h
  obtain h0 | h1 | h2 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  · exact (ZMod.val_eq_zero k).mp h0
  · rw [h1] at h
    exact absurd h (hfree v)
  · exfalso
    rw [h2] at h
    have h2' : σ (σ v) = v := h
    apply hfree v
    have := congrArg σ h2'
    rw [h3] at this
    exact this.symm

/-- The orbit relation of `σ`. -/
def orbitSetoid (h3 : ∀ v, σ (σ (σ v)) = v) : Setoid V where
  r v w := ∃ k : ZMod 3, w = sp σ k v
  iseqv := by
    refine ⟨fun v => ⟨0, (sp_zero v).symm⟩, ?_, ?_⟩
    · rintro v w ⟨k, rfl⟩
      exact ⟨-k, by rw [← sp_add h3, neg_add_cancel, sp_zero]⟩
    · rintro v w x ⟨k, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + k, by rw [sp_add h3]⟩

theorem exists_relabel (hV : Fintype.card V = 99) (h3 : ∀ v, σ (σ (σ v)) = v)
    (hfree : ∀ v, σ v ≠ v) :
    ∃ e : Fin 33 × ZMod 3 ≃ V, ∀ U b, e (U, b + 1) = σ (e (U, b)) := by
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
  have hO : Fintype.card O = 33 := by
    have h1 := Fintype.card_congr E
    rw [Fintype.card_prod, hV, ZMod.card] at h1
    omega
  let F : Fin 33 ≃ O := (Fintype.equivFinOfCardEq hO).symm
  refine ⟨(Equiv.prodCongr F (Equiv.refl _)).trans E, ?_⟩
  intro U b
  change sp σ (b + 1) (F U).out = σ (sp σ b (F U).out)
  rw [add_comm, sp_add h3, sp_one]

end relabel

/-- **Theorem 1.** A strongly regular graph with parameters `(99, 14, 1, 2)` has no automorphism of
order 3 without fixed points. -/
theorem no_free_order3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h3 : ∀ v, σ (σ (σ v)) = v) (hfree : ∀ v, σ v ≠ v) : False := by
  obtain ⟨e, he⟩ := exists_relabel (σ := σ.toEquiv) hG.card h3 hfree
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
  apply no_shift_invariant (A.submatrix e e)
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
    simp only [submatrix_apply, he, hA, SimpleGraph.adjMatrix_apply]
    have key : G.Adj (σ.toEquiv (e (U, b))) (σ.toEquiv (e (V', c))) ↔
        G.Adj (e (U, b)) (e (V', c)) := σ.map_adj_iff
    simp only [key]

end C3
