import C3formal.TriangleMain

/-!
# Proposition 2, matrix form: the discriminant of the invariant part is `≡ 1 (mod 3)`

With `B` a basis of `ker_ℤ (Ã - 3I)` (left inverse `C`):
* the fixed coordinates of `B` are divisible by 3 (`fixed_dvd`);
* `G̃ := B₁ᵀ B₁ + 3 B₂'ᵀ B₂'` is integral, `Bᵀ D B = 3 G̃`, `G̃ K = 77 I`, `det G̃ > 0`;
* modulo 3, `X = N Δ` reduces to `diag(2 (Q̄ + I), 0)` and the free-case step 5 applies on the
  32 free orbits: `det G̃ ≡ det G' ≡ 1 (mod 3)`.
-/

open Matrix

namespace C3

namespace Tri

/-- The weighted Gram matrix `G̃ = B₁ᵀ B₁ + 3 B₂'ᵀ B₂'`, where `B₂ = 3 B₂'`. -/
def Gt {r : ℕ} (B : Matrix (Fin 32 ⊕ Fin 3) (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => (∑ U : Fin 32, B (Sum.inl U) i * B (Sum.inl U) j) +
    3 * ∑ t : Fin 3, (B (Sum.inr t) i / 3) * (B (Sum.inr t) j / 3)

theorem gram_eq {r : ℕ} (B : Matrix (Fin 32 ⊕ Fin 3) (Fin r) ℤ)
    (hdiv : ∀ t j, (3 : ℤ) ∣ B (Sum.inr t) j) : Bᵀ * Dm * B = (3 : ℤ) • Gt B := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Dm, Matrix.mul_diagonal, transpose_apply, Gt, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_sum_type, wt, Sum.elim_inl, Sum.elim_inr]
  have e : ∀ t, B (Sum.inr t) i * 1 * B (Sum.inr t) j =
      3 * (3 * ((B (Sum.inr t) i / 3) * (B (Sum.inr t) j / 3))) := by
    intro t
    obtain ⟨x, hx⟩ := hdiv t i
    obtain ⟨y, hy⟩ := hdiv t j
    rw [hx, hy, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  simp only [e]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  all_goals exact Finset.sum_congr rfl fun _ _ => by ring

section main

variable {Q : Matrix (Fin 32) (Fin 32) ℤ} {a : Matrix (Fin 32) (Fin 3) ℤ}

theorem X_symm (hQs : Qᵀ = Q) (x y : Fin 32 ⊕ Fin 3) :
    Nt Q a y x * wt' x = Nt Q a x y * wt' y := by
  have h := Nt_wsymm Q a hQs x y
  rcases x with U | t <;> rcases y with V | t' <;> simp only [wt, wt', Sum.elim_inl,
    Sum.elim_inr] at h ⊢ <;> linarith

theorem DX_eq (hQs : Qᵀ = Q) : Dm * (Nt Q a * Δm) = (3 : ℤ) • (Nt Q a)ᵀ := by
  ext x y
  simp only [Dm, Δm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, transpose_apply,
    smul_eq_mul]
  have h := Nt_wsymm Q a hQs x y
  have h2 := wt_mul_wt' y
  calc wt x * (Nt Q a x y * wt' y) = (wt x * Nt Q a x y) * wt' y := by ring
    _ = (wt y * Nt Q a y x) * wt' y := by rw [h]
    _ = (wt y * wt' y) * Nt Q a y x := by ring
    _ = 3 * Nt Q a y x := by rw [h2]

theorem step5_tri (hQs : Qᵀ = Q) (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hsq : At Q a * At Q a + At Q a =
      (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw)
    (M : Matrix (Fin 32) (Fin 32) Eis) (hMh : Mᴴ = M)
    (hMM : M * M + M = (12 : Eis) • (1 : Matrix (Fin 32) (Fin 32) Eis))
    (hQM : M.map Eis.rho = Q.map φ3)
    {r : ℕ} (B : Matrix (Fin 32 ⊕ Fin 3) (Fin r) ℤ) (C : Matrix (Fin r) (Fin 32 ⊕ Fin 3) ℤ)
    (hCB : C * B = 1)
    (hXB : (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * B = 0)
    (hBC : ∀ v, (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) *ᵥ v = 0 →
      B *ᵥ (C *ᵥ v) = v) :
    0 < (Gt B).det ∧ (Gt B).det ∣ 77 ^ r ∧ ((Gt B).det : ZMod 3) = 1 ∧
      (∀ t j, (3 : ℤ) ∣ B (Sum.inr t) j) := by
  -- eigen-relations
  have hAB : At Q a * B = (3 : ℤ) • B := by
    have h := hXB
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hJB : Jw * B = 0 := Jw_mul_eig hQs hrow hsq B hAB
  have hNB : Nt Q a * B = (77 : ℤ) • B := by
    simp only [Nt, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAB, hJB,
      smul_zero]
    module
  -- divisibility of the fixed coordinates
  have hdiv : ∀ t j, (3 : ℤ) ∣ B (Sum.inr t) j := by
    intro t j
    have h := congrFun (congrFun hNB (Sum.inr t)) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h3 : (3 : ℤ) ∣ ∑ x, Nt Q a (Sum.inr t) x * B x j :=
      Finset.dvd_sum fun x _ => Dvd.dvd.mul_right (Nt_fixed_row_dvd Q a t x) _
    rw [h] at h3
    omega
  -- the matrix X = N Δ
  set X : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ := Nt Q a * Δm with hX
  clear_value X
  have hXX : (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * X = 0 := by
    rw [hX, ← Matrix.mul_assoc, X_mul_Nt hQs hrow hsq, Matrix.zero_mul]
  have hXt : Xᵀ = X := by
    ext x y
    simp only [hX, transpose_apply, Δm, Matrix.mul_diagonal]
    exact X_symm hQs x y
  have hBCX : B * C * X = X := kernel_basis_mul' hBC X hXX
  have h1 : X = X * Cᵀ * Bᵀ := by
    calc X = Xᵀ := hXt.symm
      _ = (B * C * X)ᵀ := by rw [hBCX]
      _ = Xᵀ * Cᵀ * Bᵀ := by rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
      _ = X * Cᵀ * Bᵀ := by rw [hXt]
  have hXK : X = B * (C * X * Cᵀ) * Bᵀ := by
    calc X = B * C * X := hBCX.symm
      _ = B * C * (X * Cᵀ * Bᵀ) := by rw [← h1]
      _ = B * (C * X * Cᵀ) * Bᵀ := by simp only [Matrix.mul_assoc]
  -- G̃ K = 77 I
  have hDX := DX_eq (a := a) hQs
  have h3GK : (3 : ℤ) • (Gt B * (C * X * Cᵀ)) = (231 : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ) := by
    rw [← Matrix.smul_mul, ← gram_eq B hdiv]
    calc Bᵀ * Dm * B * (C * X * Cᵀ) = Bᵀ * (Dm * (B * C * X)) * Cᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Bᵀ * ((3 : ℤ) • (Nt Q a)ᵀ) * Cᵀ := by rw [hBCX, hX, hDX]
      _ = (3 : ℤ) • ((Nt Q a * B)ᵀ * Cᵀ) := by
          rw [transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = (231 : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ) := by
          rw [hNB, transpose_smul, Matrix.smul_mul, ← transpose_mul, hCB, transpose_one, smul_smul]
          norm_num
  have hGK : Gt B * (C * X * Cᵀ) = (77 : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ) := by
    ext i j
    have h := congrFun (congrFun h3GK i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> omega
  have hdet : (Gt B).det * (C * X * Cᵀ).det = 77 ^ r := by
    rw [← det_mul, hGK, det_smul, det_one, mul_one, Fintype.card_fin]
  -- positivity
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have := congrArg (fun w => C *ᵥ w) hxy
    simpa only [mulVec_mulVec, hCB, one_mulVec] using this
  have hDpd : Dm.PosDef := by
    rw [Dm, Matrix.posDef_diagonal_iff]
    intro x
    rcases x with x | x <;> simp [wt]
  have hpos : 0 < (Gt B).det := by
    have hpd := hDpd.conjTranspose_mul_mul_same hinj
    rw [conjTranspose_eq_transpose_of_trivial, gram_eq B hdiv] at hpd
    have h := hpd.det_pos
    rw [det_smul, Fintype.card_fin] at h
    exact (mul_pos_iff_of_pos_left (by positivity)).mp h
  refine ⟨hpos, Dvd.intro _ hdet, ?_, hdiv⟩
  -- reduction modulo 3
  set P : Matrix (Fin 32) (Fin 32) (ZMod 3) := Q.map φ3 + 1 with hP
  set K := C * X * Cᵀ with hK
  have hXbar : X.map φ3 = fromBlocks ((2 : ZMod 3) • P) 0 0 0 := by
    ext (U | t) (V | t')
    · simp only [hX, Δm, Matrix.mul_diagonal, Matrix.map_apply, fromBlocks_apply₁₁, hP,
        Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply, wt', Sum.elim_inl,
        mul_one, Nt, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Jw, Matrix.of_apply, wt, At_ll, smul_eq_mul, Sum.inl.injEq, eq_intCast]
      by_cases h : U = V
      · simp only [h, ite_true]
        push_cast
        generalize ((Q V V : ℤ) : ZMod 3) = x
        revert x
        decide
      · simp only [h, ite_false]
        push_cast
        generalize ((Q U V : ℤ) : ZMod 3) = x
        revert x
        decide
    · simp only [hX, Δm, Matrix.mul_diagonal, Matrix.map_apply, fromBlocks_apply₁₂,
        Matrix.zero_apply, wt', Sum.elim_inr, eq_intCast]
      push_cast
      rw [show (3 : ZMod 3) = 0 by decide, mul_zero]
    · simp only [hX, Δm, Matrix.mul_diagonal, Matrix.map_apply, fromBlocks_apply₂₁,
        Matrix.zero_apply, wt', Sum.elim_inl, mul_one, eq_intCast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (Nt_fixed_row_dvd Q a t (Sum.inl V))
    · simp only [hX, Δm, Matrix.mul_diagonal, Matrix.map_apply, fromBlocks_apply₂₂,
        Matrix.zero_apply, wt', Sum.elim_inr, eq_intCast]
      push_cast
      rw [show (3 : ZMod 3) = 0 by decide, mul_zero]
  have hBbar : B.map φ3 = fromRows (B.toRows₁.map φ3) 0 := by
    ext (U | t) j
    · simp [toRows₁]
    · simp only [Matrix.map_apply, fromRows_apply_inr, Matrix.zero_apply, eq_intCast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (hdiv t j)
  have hCbar : C.map φ3 = fromCols (C.toCols₁.map φ3) (C.toCols₂.map φ3) := by
    ext j (U | t) <;> simp [toCols₁, toCols₂]
  have rK : K.map φ3 = C.toCols₁.map φ3 * ((2 : ZMod 3) • P) * (C.toCols₁.map φ3)ᵀ := by
    rw [hK, Matrix.map_mul, Matrix.map_mul, transpose_map, hXbar, hCbar, transpose_fromCols,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp
  have rN : (2 : ZMod 3) • P = B.toRows₁.map φ3 * K.map φ3 * (B.toRows₁.map φ3)ᵀ := by
    have h := congrArg (fun Y => Y.map φ3) hXK
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hXbar, hBbar, transpose_fromRows,
      fromRows_mul, fromRows_mul_fromCols] at h
    exact (Matrix.fromBlocks_inj.mp h).1
  -- the Eisenstein side (32 × 32)
  obtain ⟨r', B', C', hCB', hXB', hBC'⟩ :=
    exists_kernel_basis (M - (3 : Eis) • (1 : Matrix (Fin 32) (Fin 32) Eis))
  obtain ⟨hNh', hN', hdet'⟩ := M_step3n M hMh hMM B' C' hCB' hXB' hBC'
  set K' := C' * NMn M * C'ᴴ with hK'
  have rK' : K'.map Eis.rho = C'.map Eis.rho * P * (C'.map Eis.rho)ᵀ := by
    rw [hK', Matrix.map_mul, Matrix.map_mul, conjTranspose_map_rho, NMn_map Q M hQM]
  have rN' : P = B'.map Eis.rho * K'.map Eis.rho * (B'.map Eis.rho)ᵀ := by
    have h := congrArg (fun Y => Y.map Eis.rho) hN'
    rw [NMn_map Q M hQM, Matrix.map_mul, Matrix.map_mul, conjTranspose_map_rho] at h
    exact h
  have dGK : φ3 (Gt B).det * (K.map φ3).det = 2 ^ r := by
    have h := congrArg φ3 hdet
    rw [map_mul, map_pow, show φ3 77 = 2 by decide] at h
    rw [← h, RingHom.map_det φ3 K]
    rfl
  have dGK' : Eis.rho (B'ᴴ * B').det * (K'.map Eis.rho).det = 1 := by
    have h := congrArg Eis.rho hdet'
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
  obtain ⟨hrr, s, hs, hdetK⟩ :=
    core_F3_gen P (B.toRows₁.map φ3) (C.toCols₁.map φ3) (B'.map Eis.rho) (C'.map Eis.rho)
      (K.map φ3) (K'.map Eis.rho) rK rK' rN rN' hdK hdK'
  subst hrr
  have hM1 : Eis.rho (B'ᴴ * B').det = 1 := Msiden M B' C' hCB' hNh' hdet'
  rw [hM1, one_mul] at dGK'
  have hs2 : s ^ 2 = 1 := zmod3_sq_eq_one s hs
  rw [hdetK, hs2, mul_one, dGK', mul_one] at dGK
  have h2r : (2 : ZMod 3) ^ r ≠ 0 := pow_ne_zero r (by decide)
  have e1 : φ3 (Gt B).det = 1 := by
    have : φ3 (Gt B).det * 2 ^ r = 1 * 2 ^ r := by rw [dGK, one_mul]
    exact mul_right_cancel₀ h2r this
  simpa using e1

end main

end Tri

end C3
