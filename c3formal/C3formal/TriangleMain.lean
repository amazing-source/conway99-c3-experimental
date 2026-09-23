import C3formal.TriangleMatrix
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Proposition 2, matrix form: main argument

Notation of `TriangleMatrix.lean`. `B` (columns: a basis of `ker_ℤ (Ã - 3I)`) with left inverse `C`.
-/

open Matrix

namespace C3

namespace Tri

variable (Q : Matrix (Fin 32) (Fin 32) ℤ) (a : Matrix (Fin 32) (Fin 3) ℤ)

/-- `Dm = diag(w)`, `Δm = diag(w')`. -/
def Dm : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ := Matrix.diagonal wt
def Δm : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ := Matrix.diagonal wt'

/-- `N = 11 (Ã + 4 I) - 2 𝟙 wᵀ` (77 times the projector onto `ker (Ã - 3I)`). -/
def Nt : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ :=
  (11 : ℤ) • (At Q a + (4 : ℤ) • 1) - (2 : ℤ) • Jw

theorem At_mul_Jw (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14) :
    At Q a * Jw = (14 : ℤ) • Jw := by
  ext x y
  have h := congrFun hrow x
  simp only [mulVec, dotProduct, mul_one] at h
  simp only [Matrix.mul_apply, Jw, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_mul, h]

theorem Jw_mul_At (hQs : Qᵀ = Q) (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14) :
    Jw * At Q a = (14 : ℤ) • Jw := by
  ext x y
  simp only [Matrix.mul_apply, Jw, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact colw Q a hQs hrow y

theorem Jw_mul_Jw : Jw * Jw = (99 : ℤ) • Jw := by
  ext x y
  simp only [Matrix.mul_apply, Jw, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_mul, wt_sum]

/-- Weighted symmetry of `N`: `w x N x y = w y N y x`. -/
theorem Nt_wsymm (hQs : Qᵀ = Q) (x y : Fin 32 ⊕ Fin 3) :
    wt x * Nt Q a x y = wt y * Nt Q a y x := by
  have h1 := wsymm Q a hQs x y
  simp only [Nt, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Jw,
    Matrix.of_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    ring
  · simp only [hxy, Ne.symm hxy, ite_false]
    linear_combination 11 * h1

/-- The fixed rows of `N` vanish modulo 3. -/
theorem Nt_fixed_row_dvd (t : Fin 3) (x : Fin 32 ⊕ Fin 3) : (3 : ℤ) ∣ Nt Q a (Sum.inr t) x := by
  rcases x with U | t'
  · simp only [Nt, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Jw,
      Matrix.of_apply, smul_eq_mul, At_rl, wt, Sum.elim_inl]
    exact ⟨11 * a U t - 2, by simp; ring⟩
  · simp only [Nt, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Jw,
      Matrix.of_apply, smul_eq_mul, At_rr, wt, Sum.elim_inr, Sum.inr.injEq]
    by_cases h : t = t'
    · simp [h]
    · simp [h]

section main

variable {Q a}
variable (hQs : Qᵀ = Q) (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
  (hsq : At Q a * At Q a + At Q a = (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)
    + (2 : ℤ) • Jw)
include hQs hrow hsq

theorem X_mul_Nt : (At Q a - (3 : ℤ) • 1) * Nt Q a = 0 := by
  have hAJ := At_mul_Jw Q a hrow
  have hsq' : At Q a * At Q a = (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)
      + (2 : ℤ) • Jw - At Q a := by rw [← hsq]; abel
  simp only [Nt, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, hsq', hAJ]
  module

theorem Jw_mul_eig {r : ℕ} (B : Matrix (Fin 32 ⊕ Fin 3) (Fin r) ℤ)
    (hAB : At Q a * B = (3 : ℤ) • B) : Jw * B = 0 := by
  have h1 : Jw * (At Q a * B) = (3 : ℤ) • (Jw * B) := by rw [hAB, Matrix.mul_smul]
  rw [← Matrix.mul_assoc, Jw_mul_At Q a hQs hrow, Matrix.smul_mul] at h1
  ext i j
  have h := congrFun (congrFun h1 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  simp only [Matrix.zero_apply]
  linarith

end main

end Tri

end C3
