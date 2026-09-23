import C3formal.Eis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Int.Star

/-!
# Positivity of Gram determinants

`toC : ℤ[ω] → ℂ`, `ω ↦ -1/2 + i √3/2`, is an injective ring homomorphism commuting with
conjugation. Hence, for a matrix `B` over `ℤ[ω]` (or `ℤ`) with a left inverse, the Gram determinant
`det (B* B)` is a positive integer (positive definite Hermitian matrix).
-/

open Matrix
open scoped ComplexOrder

namespace Eis

/-- `ω = -1/2 + i √3/2`. -/
noncomputable def ωC : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem ωC_sq : ωC * ωC = -1 - ωC := by
  apply Complex.ext
  · simp only [ωC, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.one_re]
    nlinarith [sqrt3_mul_self]
  · simp only [ωC, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.one_im]
    ring

theorem star_ωC : star ωC = -1 - ωC := by
  apply Complex.ext <;> simp [ωC]; ring

/-- The complex embedding. -/
noncomputable def toC : Eis →+* ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * ωC
  map_one' := by simp
  map_mul' z v := by
    simp only [re_mul, im_mul]
    push_cast
    linear_combination (-((z.im : ℂ) * (v.im : ℂ))) * ωC_sq
  map_zero' := by simp
  map_add' z v := by
    simp only [re_add, im_add]
    push_cast
    ring

theorem toC_apply (z : Eis) : toC z = (z.re : ℂ) + (z.im : ℂ) * ωC := rfl

theorem toC_star (z : Eis) : toC (star z) = star (toC z) := by
  rw [toC_apply, toC_apply, star_add, star_mul', star_ωC]
  simp only [re_star, im_star]
  push_cast
  simp only [Complex.star_def, map_intCast]
  ring

theorem toC_injective : Function.Injective toC := by
  intro z v h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [toC_apply, ωC, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im] at him hre
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (z.im : ℝ) = v.im := by nlinarith
  have h2 : z.im = v.im := by exact_mod_cast h1
  have h3 : (z.re : ℝ) = v.re := by rw [h1] at hre; linarith
  have h4 : z.re = v.re := by exact_mod_cast h3
  ext <;> assumption

/-- For `B` over `ℤ[ω]` with a left inverse, `det (Bᴴ B)` is a positive rational integer. -/
theorem det_gram_pos {n r : ℕ} (B : Matrix (Fin n) (Fin r) Eis) (C : Matrix (Fin r) (Fin n) Eis)
    (hCB : C * B = 1) : ∃ d : ℤ, 0 < d ∧ (Bᴴ * B).det = d := by
  have hstar : star (Bᴴ * B).det = (Bᴴ * B).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨((Bᴴ * B).det).re, ?_, eq_intCast_of_star_eq hstar⟩
  set BC := B.map toC with hBC
  have hCBC : C.map toC * BC = 1 := by
    rw [hBC, ← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero toC) (map_one toC)]
  have hinj : Function.Injective BC.mulVec := by
    intro x y hxy
    have := congrArg (fun w => C.map toC *ᵥ w) hxy
    simpa only [mulVec_mulVec, hCBC, one_mulVec] using this
  have hpd : (BCᴴ * BC).PosDef := Matrix.PosDef.conjTranspose_mul_self BC hinj
  have hdet := hpd.det_pos
  have hmap : BCᴴ * BC = (Bᴴ * B).map toC := by
    rw [Matrix.map_mul, hBC]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, toC_star]
  rw [hmap] at hdet
  set d : ℤ := ((Bᴴ * B).det).re with hddef
  have hd : (Bᴴ * B).det = (d : Eis) := eq_intCast_of_star_eq hstar
  have hval : ((Bᴴ * B).map toC).det = ((d : ℤ) : ℂ) := by
    have h1 : toC (Bᴴ * B).det = ((Bᴴ * B).map toC).det := RingHom.map_det toC (Bᴴ * B)
    rw [← h1, hd, map_intCast]
  rw [hval] at hdet
  have h2 : (0 : ℝ) < ((d : ℤ) : ℂ).re := (Complex.pos_iff.mp hdet).1
  have h3 : (0 : ℝ) < (d : ℝ) := by simpa using h2
  exact_mod_cast h3

end Eis
