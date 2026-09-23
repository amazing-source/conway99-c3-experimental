import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Step 2: integral bases of kernels (saturated lattices)

Over a principal ideal domain `R`, the kernel `L = {v ∈ Rⁿ : X v = 0}` of a square matrix `X` is a
direct summand of `Rⁿ`: there are matrices `B` (whose columns form a basis of `L`) and `C` with
`C B = I`. We obtain them from the Smith normal form of `L ⊆ Rⁿ`: the columns of `B` are the vectors
`bM (f i)` of the adapted basis, which lie in `L` because `L` is saturated (`a • x ∈ L`, `a ≠ 0`
forces `x ∈ L`), and the rows of `C` are the corresponding coordinate functionals.

Step 3 (`gram_identities`) then turns `B C N = N`, `N B = c B`, `N* = N` into `N = B K B*` and
`G K = c I` with `K = C N C*`, `G = B* B`.
-/

open Matrix Module

namespace C3

theorem exists_kernel_basis {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : ℕ} (X : Matrix (Fin n) (Fin n) R) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) R) (C : Matrix (Fin r) (Fin n) R),
      C * B = 1 ∧ X * B = 0 ∧ ∀ v : Fin n → R, X *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v := by
  classical
  set N : Submodule R (Fin n → R) := LinearMap.ker (Matrix.mulVecLin X) with hNdef
  obtain ⟨k, snf⟩ := N.smithNormalForm (Pi.basisFun R (Fin n))
  set bM := snf.bM
  set f := snf.f
  set Bm : Matrix (Fin n) (Fin k) R := Matrix.of fun a i => bM (f i) a with hBm
  set Cm : Matrix (Fin k) (Fin n) R := Matrix.of fun i a => bM.repr (Pi.single a 1) (f i) with hCm
  -- `C v` computes the coordinates of `v` along `bM ∘ f`.
  have hCv : ∀ v : Fin n → R, Cm *ᵥ v = fun i => bM.repr v (f i) := by
    intro v
    ext i
    have hv : v = ∑ a, v a • (Pi.single a 1 : Fin n → R) := by
      ext b
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hCm, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  -- the columns of `B` lie in the kernel
  have hcol : ∀ i, X *ᵥ bM (f i) = 0 := by
    intro i
    have hmem : (snf.bN i : Fin n → R) ∈ N := (snf.bN i).2
    rw [snf.snf i] at hmem
    have ha : snf.a i ≠ 0 := by
      intro h0
      have : (snf.bN i : Fin n → R) = 0 := by rw [snf.snf i, h0, zero_smul]
      exact snf.bN.ne_zero i (Subtype.ext this)
    have h1 : snf.a i = 0 ∨ X *ᵥ bM (f i) = 0 := by
      simpa [hNdef] using hmem
    exact h1.resolve_left ha
  refine ⟨k, Bm, Cm, ?_, ?_, ?_⟩
  · -- `C B = 1`
    ext i j
    have h := congrFun (hCv (bM (f j))) i
    have e : (Cm * Bm) i j = (Cm *ᵥ bM (f j)) i := by
      simp only [Matrix.mul_apply, mulVec, dotProduct, hBm, Matrix.of_apply]
    rw [e, h, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp only [f.injective.eq_iff, eq_comm]
  · -- `X B = 0`
    ext a i
    have e : (X * Bm) a i = (X *ᵥ bM (f i)) a := by
      simp only [Matrix.mul_apply, mulVec, dotProduct, hBm, Matrix.of_apply]
    rw [e, hcol i]
    rfl
  · -- `B C v = v` on the kernel
    intro v hv
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

/-- Column version: `B C Y = Y` whenever all columns of `Y` lie in the kernel. -/
theorem kernel_basis_mul {R : Type*} [CommRing R] {n r : ℕ} {m : Type*}
    {X : Matrix (Fin n) (Fin n) R} {B : Matrix (Fin n) (Fin r) R} {C : Matrix (Fin r) (Fin n) R}
    (h : ∀ v : Fin n → R, X *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v)
    (Y : Matrix (Fin n) m R) (hY : X * Y = 0) : B * C * Y = Y := by
  ext a j
  have hcol : X *ᵥ (fun i => Y i j) = 0 := by
    ext i
    have := congrFun (congrFun hY i) j
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this
  have := congrFun (h _ hcol) a
  rw [Matrix.mul_assoc]
  simpa [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum] using this

/-- **Step 3.** From `C B = I`, `B C N = N`, `N B = c B` and `N* = N` (with `c` self-adjoint):
`N = B K B*` and `G K = c I`, where `K = C N C*` and `G = B* B`. -/
theorem gram_identities {R : Type*} [CommRing R] [StarRing R] {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) R) (C : Matrix (Fin r) (Fin n) R) (N : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : star c = c) (hCB : C * B = 1) (hBCN : B * C * N = N) (hNB : N * B = c • B)
    (hNh : Nᴴ = N) :
    N = B * (C * N * Cᴴ) * Bᴴ ∧ (Bᴴ * B) * (C * N * Cᴴ) = c • (1 : Matrix (Fin r) (Fin r) R) := by
  have hN2 : N = N * Cᴴ * Bᴴ := by
    calc N = Nᴴ := hNh.symm
      _ = (B * C * N)ᴴ := by rw [hBCN]
      _ = Nᴴ * Cᴴ * Bᴴ := by rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = N * Cᴴ * Bᴴ := by rw [hNh]
  have hBN : Bᴴ * N = c • Bᴴ := by
    calc Bᴴ * N = (Nᴴ * B)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
      _ = (N * B)ᴴ := by rw [hNh]
      _ = c • Bᴴ := by rw [hNB, conjTranspose_smul, hc]
  constructor
  · calc N = B * C * N := hBCN.symm
      _ = B * C * (N * Cᴴ * Bᴴ) := by rw [← hN2]
      _ = B * (C * N * Cᴴ) * Bᴴ := by simp only [Matrix.mul_assoc]
  · calc (Bᴴ * B) * (C * N * Cᴴ) = Bᴴ * (B * C * N) * Cᴴ := by simp only [Matrix.mul_assoc]
      _ = Bᴴ * N * Cᴴ := by rw [hBCN]
      _ = c • (Bᴴ * Cᴴ) := by rw [hBN, Matrix.smul_mul]
      _ = c • (C * B)ᴴ := by rw [conjTranspose_mul]
      _ = c • (1 : Matrix (Fin r) (Fin r) R) := by rw [hCB, conjTranspose_one]

end C3
