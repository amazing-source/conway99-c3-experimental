import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Step 2 for an arbitrary finite index type

Same statements as `C3formal/Saturated.lean`, with the index type `Fin n` replaced by any finite
type `ι` (used for the fixed-triangle case, where vertices of the quotient are `Fin 32 ⊕ Fin 3`).
-/

open Matrix Module

namespace C3

theorem exists_kernel_basis' {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι R) :
    ∃ (r : ℕ) (B : Matrix ι (Fin r) R) (C : Matrix (Fin r) ι R),
      C * B = 1 ∧ X * B = 0 ∧ ∀ v : ι → R, X *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v := by
  classical
  set N : Submodule R (ι → R) := LinearMap.ker (Matrix.mulVecLin X) with hNdef
  obtain ⟨k, snf⟩ := N.smithNormalForm (Pi.basisFun R ι)
  set bM := snf.bM
  set f := snf.f
  set Bm : Matrix ι (Fin k) R := Matrix.of fun a i => bM (f i) a with hBm
  set Cm : Matrix (Fin k) ι R := Matrix.of fun i a => bM.repr (Pi.single a 1) (f i) with hCm
  have hCv : ∀ v : ι → R, Cm *ᵥ v = fun i => bM.repr v (f i) := by
    intro v
    ext i
    have hv : v = ∑ a, v a • (Pi.single a 1 : ι → R) := by
      ext b
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hCm, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hcol : ∀ i, X *ᵥ bM (f i) = 0 := by
    intro i
    have hmem : (snf.bN i : ι → R) ∈ N := (snf.bN i).2
    rw [snf.snf i] at hmem
    have ha : snf.a i ≠ 0 := by
      intro h0
      have : (snf.bN i : ι → R) = 0 := by rw [snf.snf i, h0, zero_smul]
      exact snf.bN.ne_zero i (Subtype.ext this)
    have h1 : snf.a i = 0 ∨ X *ᵥ bM (f i) = 0 := by
      simpa [hNdef] using hmem
    exact h1.resolve_left ha
  refine ⟨k, Bm, Cm, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (hCv (bM (f j))) i
    have e : (Cm * Bm) i j = (Cm *ᵥ bM (f j)) i := by
      simp only [Matrix.mul_apply, mulVec, dotProduct, hBm, Matrix.of_apply]
    rw [e, h, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp only [f.injective.eq_iff, eq_comm]
  · ext a i
    have e : (X * Bm) a i = (X *ᵥ bM (f i)) a := by
      simp only [Matrix.mul_apply, mulVec, dotProduct, hBm, Matrix.of_apply]
    rw [e, hcol i]
    rfl
  · intro v hv
    have hvN : v ∈ N := by simpa [hNdef] using hv
    rw [hCv v]
    have hsum : v = ∑ m, bM.repr v m • bM m := (bM.sum_repr v).symm
    conv_rhs => rw [hsum]
    ext a
    simp only [mulVec, dotProduct, hBm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    refine Fintype.sum_of_injective f f.injective _ _ ?_ ?_
    · intro m hm
      rw [snf.repr_eq_zero_of_notMem_range ⟨v, hvN⟩ hm, zero_mul]
    · intro i
      rw [mul_comm]

theorem kernel_basis_mul' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {r : ℕ} {m : Type*}
    {X : Matrix ι ι R} {B : Matrix ι (Fin r) R} {C : Matrix (Fin r) ι R}
    (h : ∀ v : ι → R, X *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v)
    (Y : Matrix ι m R) (hY : X * Y = 0) : B * C * Y = Y := by
  ext a j
  have hcol : X *ᵥ (fun i => Y i j) = 0 := by
    ext i
    have := congrFun (congrFun hY i) j
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this
  have := congrFun (h _ hcol) a
  rw [Matrix.mul_assoc]
  simpa [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum] using this

end C3
