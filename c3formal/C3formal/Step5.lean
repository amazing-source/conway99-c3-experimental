import C3formal.Eis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod

/-!
# Step 5: the two discriminants agree modulo 3

This is the new ingredient of the argument (see `pdf/preuve_c3.pdf`, Étape 5).

Setting. `Q` is a symmetric integer `33 × 33` matrix and `M` a Hermitian `33 × 33` matrix over the
Eisenstein integers with `M ≡ Q (mod 1 - ω)`. Put
* `N  = 11 (Q + 4 I) - 6 J`  (77 times the projector onto `ker (Q - 3I)`),
* `N' = M + 4 I`             (7 times the projector onto `ker (M - 3I)`).
Step 3 of the proof produces integral matrices `B, C` (resp. `B', C'` over `ℤ[ω]`) with
`N = B K Bᵀ`, `G K = 77 I` where `K = C N Cᵀ`, `G = Bᵀ B`
(resp. `N' = B' K' B'ᴴ`, `G' K' = 7 I` where `K' = C' N' C'ᴴ`, `G' = B'ᴴ B'`).

Statement. Under these identities, `r = r'` and `det G ≡ det G' (mod 3)`, where the right-hand
side is reduced by `ρ : ℤ[ω] → 𝔽₃`, `ω ↦ 1`.

The proof reduces everything to `𝔽₃`: there `N̄ = 2 N̄'` (because `11 ≡ 2`, `6 ≡ 0`, `4 ≡ 1` and
`M ≡ Q`), so the two reduced Gram forms are the same quadratic space up to the factor 2.
-/

open Matrix

namespace C3

/-- The all-ones matrix. -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun _ _ => 1

/-- `N = 11 (Q + 4 I) - 6 J`. -/
def NQ (Q : Matrix (Fin 33) (Fin 33) ℤ) : Matrix (Fin 33) (Fin 33) ℤ :=
  (11 : ℤ) • (Q + (4 : ℤ) • (1 : Matrix (Fin 33) (Fin 33) ℤ)) - (6 : ℤ) • J 33

/-- `N' = M + 4 I`. -/
def NM (M : Matrix (Fin 33) (Fin 33) Eis) : Matrix (Fin 33) (Fin 33) Eis :=
  M + (4 : Eis) • (1 : Matrix (Fin 33) (Fin 33) Eis)

/-! ### The core statement over `𝔽₃` -/

section core

theorem zmod3_sq_eq_one : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by decide

theorem two_smul_two_smul {m n : Type*} (A : Matrix m n (ZMod 3)) :
    (2 : ZMod 3) • ((2 : ZMod 3) • A) = A := by
  rw [smul_smul]
  have h : (2 : ZMod 3) * 2 = 1 := by decide
  rw [h, one_smul]

/-- Core of step 5 over `𝔽₃`: if `K = C (2P) Cᵀ`, `K' = C' P C'ᵀ`, `2P = B K Bᵀ`,
`P = B' K' B'ᵀ` with
`K`, `K'` invertible, then the sizes agree and `det K = 2^r s² det K'` with `s ≠ 0`. -/
theorem core_F3 {r r' : ℕ}
    (P : Matrix (Fin 33) (Fin 33) (ZMod 3))
    (B : Matrix (Fin 33) (Fin r) (ZMod 3)) (C : Matrix (Fin r) (Fin 33) (ZMod 3))
    (B' : Matrix (Fin 33) (Fin r') (ZMod 3)) (C' : Matrix (Fin r') (Fin 33) (ZMod 3))
    (K : Matrix (Fin r) (Fin r) (ZMod 3)) (K' : Matrix (Fin r') (Fin r') (ZMod 3))
    (hK : K = C * ((2 : ZMod 3) • P) * Cᵀ) (hK' : K' = C' * P * C'ᵀ)
    (hN : (2 : ZMod 3) • P = B * K * Bᵀ) (hN' : P = B' * K' * B'ᵀ)
    (hdK : K.det ≠ 0) (hdK' : K'.det ≠ 0) :
    r = r' ∧ ∃ s : ZMod 3, s ≠ 0 ∧ K.det = 2 ^ r * s ^ 2 * K'.det := by
  have eK : K = ((2 : ZMod 3) • (C * B')) * K' * (C * B')ᵀ := by
    rw [hK, hN', Matrix.transpose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hP : P = (2 : ZMod 3) • (B * K * Bᵀ) := by
    rw [← hN, two_smul_two_smul]
  have eK' : K' = ((2 : ZMod 3) • (C' * B)) * K * (C' * B)ᵀ := by
    rw [hK', hP, Matrix.transpose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hr : r ≤ r' := by
    have h1 : K.rank = r := by rw [rank_of_det_ne_zero hdK, Fintype.card_fin]
    calc r = K.rank := h1.symm
      _ = (((2 : ZMod 3) • (C * B')) * K' * (C * B')ᵀ).rank := by rw [← eK]
      _ ≤ (((2 : ZMod 3) • (C * B')) * K').rank := rank_mul_le_left _ _
      _ ≤ ((2 : ZMod 3) • (C * B')).rank := rank_mul_le_left _ _
      _ ≤ r' := rank_le_width _
  have hr' : r' ≤ r := by
    have h1 : K'.rank = r' := by rw [rank_of_det_ne_zero hdK', Fintype.card_fin]
    calc r' = K'.rank := h1.symm
      _ = (((2 : ZMod 3) • (C' * B)) * K * (C' * B)ᵀ).rank := by rw [← eK']
      _ ≤ (((2 : ZMod 3) • (C' * B)) * K).rank := rank_mul_le_left _ _
      _ ≤ ((2 : ZMod 3) • (C' * B)).rank := rank_mul_le_left _ _
      _ ≤ r := rank_le_width _
  obtain rfl : r = r' := le_antisymm hr hr'
  refine ⟨rfl, (C * B').det, ?_, ?_⟩
  · intro h0
    apply hdK
    rw [eK, det_mul, det_mul, det_smul, det_transpose, h0]
    ring
  · rw [eK, det_mul, det_mul, det_smul, det_transpose, Fintype.card_fin]
    ring

end core

/-! ### Reduction of the integral and Eisenstein identities to `𝔽₃` -/

section reduction

/-- Reduction modulo 3 of integers. -/
abbrev φ3 : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)

theorem conjTranspose_map_rho {m n : Type*} (A : Matrix m n Eis) :
    Aᴴ.map Eis.rho = (A.map Eis.rho)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem NQ_map (Q : Matrix (Fin 33) (Fin 33) ℤ) :
    (NQ Q).map φ3 = (2 : ZMod 3) • (Q.map φ3 + 1) := by
  ext i j
  simp only [NQ, J, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul, eq_intCast]
  by_cases h : i = j
  · simp only [h, ite_true]
    push_cast
    generalize ((Q j j : ℤ) : ZMod 3) = x
    revert x
    decide
  · simp only [h, ite_false]
    push_cast
    generalize ((Q i j : ℤ) : ZMod 3) = x
    revert x
    decide

theorem NM_map (Q : Matrix (Fin 33) (Fin 33) ℤ) (M : Matrix (Fin 33) (Fin 33) Eis)
    (hQM : M.map Eis.rho = Q.map φ3) :
    (NM M).map Eis.rho = Q.map φ3 + 1 := by
  ext i j
  have hij := congrFun (congrFun hQM i) j
  simp only [Matrix.map_apply] at hij
  simp only [NM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, map_add, map_mul, hij]
  have h4 : Eis.rho 4 = 1 := by
    rw [Eis.rho_apply]
    decide
  split_ifs <;> simp [h4]

/-- **Step 5.** The integral identities of step 3 force `r = r'` and `det G ≡ det G' (mod 3)`. -/
theorem step5 {r r' : ℕ}
    (Q : Matrix (Fin 33) (Fin 33) ℤ) (M : Matrix (Fin 33) (Fin 33) Eis)
    (hQM : M.map Eis.rho = Q.map φ3)
    (B : Matrix (Fin 33) (Fin r) ℤ) (C : Matrix (Fin r) (Fin 33) ℤ)
    (B' : Matrix (Fin 33) (Fin r') Eis) (C' : Matrix (Fin r') (Fin 33) Eis)
    (hN : NQ Q = B * (C * NQ Q * Cᵀ) * Bᵀ)
    (hGK : ((Bᵀ * B) * (C * NQ Q * Cᵀ)).det = 77 ^ r)
    (hN' : NM M = B' * (C' * NM M * C'ᴴ) * B'ᴴ)
    (hGK' : ((B'ᴴ * B') * (C' * NM M * C'ᴴ)).det = 7 ^ r') :
    r = r' ∧ ((Bᵀ * B).det : ZMod 3) = Eis.rho (B'ᴴ * B').det := by
  set K := C * NQ Q * Cᵀ with hKdef
  set K' := C' * NM M * C'ᴴ with hK'def
  set P : Matrix (Fin 33) (Fin 33) (ZMod 3) := Q.map φ3 + 1 with hPdef
  -- reduced identities
  have rK : K.map φ3 = C.map φ3 * ((2 : ZMod 3) • P) * (C.map φ3)ᵀ := by
    rw [hKdef, Matrix.map_mul, Matrix.map_mul, transpose_map, NQ_map]
  have rK' : K'.map Eis.rho = C'.map Eis.rho * P * (C'.map Eis.rho)ᵀ := by
    rw [hK'def, Matrix.map_mul, Matrix.map_mul, conjTranspose_map_rho, NM_map Q M hQM]
  have rN : (2 : ZMod 3) • P = B.map φ3 * K.map φ3 * (B.map φ3)ᵀ := by
    have := congrArg (fun X => X.map φ3) hN
    rw [NQ_map, Matrix.map_mul, Matrix.map_mul, transpose_map] at this
    exact this
  have rN' : P = B'.map Eis.rho * K'.map Eis.rho * (B'.map Eis.rho)ᵀ := by
    have := congrArg (fun X => X.map Eis.rho) hN'
    rw [NM_map Q M hQM, Matrix.map_mul, Matrix.map_mul, conjTranspose_map_rho] at this
    exact this
  -- determinants
  have dGK : φ3 (Bᵀ * B).det * (K.map φ3).det = 2 ^ r := by
    have h := congrArg φ3 hGK
    rw [det_mul, map_mul, map_pow, show φ3 77 = 2 by decide] at h
    rw [← h, RingHom.map_det φ3 K]
    rfl
  have dGK' : Eis.rho (B'ᴴ * B').det * (K'.map Eis.rho).det = 1 := by
    have h := congrArg Eis.rho hGK'
    have h7 : Eis.rho 7 = 1 := by
      rw [Eis.rho_apply]
      decide
    rw [det_mul, map_mul, map_pow, h7, one_pow] at h
    rw [← h, RingHom.map_det Eis.rho K']
    rfl
  have hdK : (K.map φ3).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at dGK
    exact absurd dGK.symm (pow_ne_zero r (by decide))
  have hdK' : (K'.map Eis.rho).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at dGK'
    exact zero_ne_one dGK'
  obtain ⟨hrr, s, hs, hdet⟩ :=
    core_F3 P (B.map φ3) (C.map φ3) (B'.map Eis.rho) (C'.map Eis.rho) (K.map φ3) (K'.map Eis.rho)
      rK rK' rN rN' hdK hdK'
  subst hrr
  refine ⟨rfl, ?_⟩
  have hs2 : s ^ 2 = 1 := zmod3_sq_eq_one s hs
  rw [hdet, hs2, mul_one] at dGK
  -- dGK : φ3 det G * (2^r * det K̄') = 2^r ; dGK' : ρ det G' * det K̄' = 1
  have h2r : (2 : ZMod 3) ^ r ≠ 0 := pow_ne_zero r (by decide)
  have e1 : φ3 (Bᵀ * B).det * (K'.map Eis.rho).det = 1 := by
    have : (2 : ZMod 3) ^ r * (φ3 (Bᵀ * B).det * (K'.map Eis.rho).det) = 2 ^ r * 1 := by
      linear_combination dGK
    exact mul_left_cancel₀ h2r this
  have e2 : φ3 (Bᵀ * B).det = Eis.rho (B'ᴴ * B').det :=
    mul_right_cancel₀ hdK' (e1.trans dGK'.symm)
  simpa using e2

end reduction

end C3
