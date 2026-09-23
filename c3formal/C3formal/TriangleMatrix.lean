import C3formal.GenLemmas
import C3formal.SaturatedGen
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases

/-!
# Proposition 2 (automorphism of order 3 fixing a triangle), matrix form

Index set `ι = Fin 32 ⊕ Fin 3`: the 32 free orbits and the 3 fixed vertices. On `g`-invariant
vectors the adjacency matrix acts by `Ã = [[Q, a], [3 aᵀ, J₃ - I₃]]`, which is self-adjoint for the
weights `w = (3, …, 3, 1, 1, 1)`, satisfies `Ã 𝟙 = 14 𝟙` and `Ã² + Ã = 12 I + 2 𝟙 wᵀ`.
`M` (32 × 32, Eisenstein) is the `ω`-part, `M ≡ Q (mod 1 - ω)`.

Key new point (no appeal to Ishida's identity): the fixed coordinates of every invariant integral
3-eigenvector are divisible by 3, because the corresponding rows of `77 E₃` are `≡ 0 (mod 3)`.
Hence the weighted Gram matrix `G̃ = B₁ᵀ B₁ + 3 B₂'ᵀ B₂'` is integral, and the argument of the free
case goes through: `det G̃ ≡ det G' (mod 3)`, `det G' ≡ 1`, `det G̃ ≡ 2`.
-/

open Matrix

namespace C3

namespace Tri

/-- Weights of the invariant form: 3 on free orbits, 1 on fixed points. -/
def wt : Fin 32 ⊕ Fin 3 → ℤ := Sum.elim (fun _ => 3) (fun _ => 1)

/-- Complementary weights: 1 on free orbits, 3 on fixed points (`wt * wt' = 3`). -/
def wt' : Fin 32 ⊕ Fin 3 → ℤ := Sum.elim (fun _ => 1) (fun _ => 3)

/-- `𝟙 wᵀ`. -/
def Jw : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ := Matrix.of fun _ y => wt y

/-- The all-ones `3 × 3` matrix. -/
def J3 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun _ _ => 1

/-- The action of `A` on invariant vectors. -/
def At (Q : Matrix (Fin 32) (Fin 32) ℤ) (a : Matrix (Fin 32) (Fin 3) ℤ) :
    Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ :=
  Matrix.fromBlocks Q a ((3 : ℤ) • aᵀ) (J3 - 1)

theorem wt_sum : ∑ x, wt x = 99 := by
  simp [wt, Fintype.sum_sum_type]

theorem wt_mul_wt' (x : Fin 32 ⊕ Fin 3) : wt x * wt' x = 3 := by
  rcases x with x | x <;> simp [wt, wt']

section structure_lemmas

variable (Q : Matrix (Fin 32) (Fin 32) ℤ) (a : Matrix (Fin 32) (Fin 3) ℤ)

@[simp] theorem At_ll (U V : Fin 32) : At Q a (Sum.inl U) (Sum.inl V) = Q U V := rfl
@[simp] theorem At_lr (U : Fin 32) (t : Fin 3) : At Q a (Sum.inl U) (Sum.inr t) = a U t := rfl
@[simp] theorem At_rl (t : Fin 3) (U : Fin 32) :
    At Q a (Sum.inr t) (Sum.inl U) = 3 * a U t := by
  simp [At]
@[simp] theorem At_rr (t t' : Fin 3) :
    At Q a (Sum.inr t) (Sum.inr t') = if t = t' then 0 else 1 := by
  simp only [At, fromBlocks_apply₂₂, Matrix.sub_apply, J3, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- Weighted column sums: `wᵀ Ã = 14 wᵀ`. -/
theorem colw (hQs : Qᵀ = Q) (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (y : Fin 32 ⊕ Fin 3) : ∑ x, wt x * At Q a x y = 14 * wt y := by
  have hrowe : ∀ x, ∑ z, At Q a x z = 14 := fun x => by
    simpa [mulVec, dotProduct] using congrFun hrow x
  rcases y with V | t
  · have h := hrowe (Sum.inl V)
    rw [Fintype.sum_sum_type] at h ⊢
    simp only [At_ll, At_lr, At_rl, wt, Sum.elim_inl, Sum.elim_inr] at h ⊢
    have hsymQ : ∀ U, Q U V = Q V U := fun U => by
      have := congrFun (congrFun hQs V) U
      simpa [transpose_apply] using this
    simp only [hsymQ]
    rw [← Finset.mul_sum]
    simp only [one_mul]
    rw [← Finset.mul_sum]
    linarith
  · have h := hrowe (Sum.inr t)
    rw [Fintype.sum_sum_type] at h ⊢
    simp only [At_lr, At_rl, At_rr, wt, Sum.elim_inl, Sum.elim_inr] at h ⊢
    have hs : ∑ t' : Fin 3, (1 : ℤ) * (if t' = t then 0 else 1) =
        ∑ t' : Fin 3, (if t = t' then 0 else 1) := by
      refine Finset.sum_congr rfl fun t' _ => ?_
      by_cases htt : t' = t
      · simp [htt]
      · simp [htt, Ne.symm htt]
    rw [hs]
    have h3 : ∑ U : Fin 32, 3 * a U t = ∑ U : Fin 32, 3 * a U t := rfl
    linarith

/-- `D Ã` is symmetric, with `D = diag(w)`. -/
theorem wsymm (hQs : Qᵀ = Q) (x y : Fin 32 ⊕ Fin 3) :
    wt x * At Q a x y = wt y * At Q a y x := by
  rcases x with U | t <;> rcases y with V | t'
  · have := congrFun (congrFun hQs V) U
    simp only [transpose_apply] at this
    simp [wt, this]
  · simp [wt]
  · simp [wt]
  · simp only [At_rr, wt, Sum.elim_inr, one_mul]
    by_cases h : t = t'
    · simp [h]
    · simp [h, Ne.symm h]

end structure_lemmas

end Tri

end C3
