import C3formal.TriangleStep5

/-!
# Proposition 2, matrix form: `det G̃ ≡ 2 (mod 3)` (the prime 11)

`P₂ = 54 I - 18 Ã + 2 𝟙 wᵀ = (Ã - 3)(Ã - 14)`; `W = ker_ℤ P₂` contains
`ker (Ã - 3)` and `𝟙`. `N_W = 9 (Ã + 4) - 𝟙 wᵀ` is `63` times the projector onto `W`, so the weighted
Gram matrix `G_W = B_Wᵀ D B_W` divides `189^{r_W}` and `11 ∤ det G_W`. The lattice
`ker (Ã - 3) ⊕ ℤ 𝟙` has Gram matrix `diag(3 G̃, 99)`, hence `99 · 3^r · det G̃ = det(T)² · det G_W`:
the 11-adic valuation of `det G̃` is odd and `det G̃ ≡ 2 (mod 3)`.
-/

open Matrix

namespace C3

namespace Tri

/-- The all-ones vector on the invariant coordinates. -/
def onesT : Fin 32 ⊕ Fin 3 → ℤ := fun _ => 1

theorem Dm_transpose : Dmᵀ = Dm := by
  unfold Dm
  exact diagonal_transpose wt

theorem wsym_symm (N : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)
    (h : ∀ x y, wt x * N x y = wt y * N y x) : (N * Δm)ᵀ = N * Δm := by
  ext x y
  simp only [transpose_apply, Δm, Matrix.mul_diagonal]
  have hxy := h x y
  rcases x with U | t <;> rcases y with V | t' <;>
    simp only [wt, wt', Sum.elim_inl, Sum.elim_inr] at hxy ⊢ <;> linarith

theorem wsym_D (N : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)
    (h : ∀ x y, wt x * N x y = wt y * N y x) : Dm * (N * Δm) = (3 : ℤ) • Nᵀ := by
  ext x y
  simp only [Dm, Δm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, transpose_apply,
    smul_eq_mul]
  have hxy := h x y
  have h2 := wt_mul_wt' y
  calc wt x * (N x y * wt' y) = (wt x * N x y) * wt' y := by ring
    _ = (wt y * N y x) * wt' y := by rw [hxy]
    _ = (wt y * wt' y) * N y x := by ring
    _ = 3 * N y x := by rw [h2]

section main

variable {Q : Matrix (Fin 32) (Fin 32) ℤ} {a : Matrix (Fin 32) (Fin 3) ℤ}

theorem step4_tri (hQs : Qᵀ = Q) (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hsq : At Q a * At Q a + At Q a =
      (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw)
    {r : ℕ} (B : Matrix (Fin 32 ⊕ Fin 3) (Fin r) ℤ) (C : Matrix (Fin r) (Fin 32 ⊕ Fin 3) ℤ)
    (hCB : C * B = 1)
    (hXB : (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * B = 0)
    (hBC : ∀ v, (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) *ᵥ v = 0 →
      B *ᵥ (C *ᵥ v) = v)
    (hdiv : ∀ t j, (3 : ℤ) ∣ B (Sum.inr t) j) (hpos : 0 < (Gt B).det)
    (hdvd : (Gt B).det ∣ 77 ^ r) : ((Gt B).det : ZMod 3) = 2 := by
  have hAJ := At_mul_Jw Q a hrow
  have hJA := Jw_mul_At Q a hQs hrow
  have hJJ := Jw_mul_Jw
  have hsq' : At Q a * At Q a =
      (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw - At Q a := by
    rw [← hsq]; abel
  have hAB : At Q a * B = (3 : ℤ) • B := by
    have h := hXB
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hJB : Jw * B = 0 := Jw_mul_eig hQs hrow hsq B hAB
  -- the lattice W = ker P₂
  set P2 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ :=
    (54 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) - (18 : ℤ) • At Q a + (2 : ℤ) • Jw
    with hP2
  clear_value P2
  obtain ⟨rW, BW, CW, hCBW, hXBW, hBCW⟩ := exists_kernel_basis' P2
  have hJBW : Jw * BW = (9 : ℤ) •
      ((At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * BW) := by
    have h0 := hXBW
    rw [hP2] at h0
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h0
    ext i j
    have h := congrFun (congrFun h0 i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at h
    simp only [Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.one_mul, smul_eq_mul]
    linarith
  -- N_W = 63 × (projector onto W)
  set NW : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ :=
    (9 : ℤ) • (At Q a + (4 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) - Jw with hNW
  clear_value NW
  have hXNW : P2 * NW = 0 := by
    rw [hP2, hNW]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hJA, hJJ, hsq', hAJ]
    module
  have hNWB : NW * BW = (63 : ℤ) • BW := by
    rw [hNW]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, hJBW]
    module
  have hNWsym : ∀ x y, wt x * NW x y = wt y * NW y x := by
    intro x y
    have h1 := wsymm Q a hQs x y
    rw [hNW]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Jw,
      Matrix.of_apply, smul_eq_mul]
    by_cases hxy : x = y
    · subst hxy
      ring
    · simp only [hxy, Ne.symm hxy, ite_false]
      linear_combination 9 * h1
  set XW := NW * Δm with hXW
  clear_value XW
  have hXXW : P2 * XW = 0 := by rw [hXW, ← Matrix.mul_assoc, hXNW, Matrix.zero_mul]
  have hDXW : Dm * XW = (3 : ℤ) • NWᵀ := by rw [hXW]; exact wsym_D NW hNWsym
  have hBCXW : BW * CW * XW = XW := kernel_basis_mul' hBCW XW hXXW
  have hGKW : (BWᵀ * Dm * BW) * (CW * XW * CWᵀ) =
      (189 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ) := by
    calc (BWᵀ * Dm * BW) * (CW * XW * CWᵀ) = BWᵀ * (Dm * (BW * CW * XW)) * CWᵀ := by
          simp only [Matrix.mul_assoc]
      _ = BWᵀ * ((3 : ℤ) • NWᵀ) * CWᵀ := by rw [hBCXW, hDXW]
      _ = (3 : ℤ) • ((NW * BW)ᵀ * CWᵀ) := by
          rw [transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = (189 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ) := by
          rw [hNWB, transpose_smul, Matrix.smul_mul, ← transpose_mul, hCBW, transpose_one,
            smul_smul]
          norm_num
  have hdetW : (BWᵀ * Dm * BW).det * (CW * XW * CWᵀ).det = 189 ^ rW := by
    rw [← det_mul, hGKW, det_smul, det_one, mul_one, Fintype.card_fin]
  have h11W : ¬ (11 : ℤ) ∣ (BWᵀ * Dm * BW).det := by
    intro h11
    have h1 : (11 : ℤ) ∣ 189 ^ rW := dvd_trans h11 (Dvd.intro _ hdetW)
    have h2 : (11 : ℕ) ∣ 189 ^ rW := by exact_mod_cast h1
    have h3 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h2
    norm_num at h3
  -- B1 = [B | 𝟙]
  have hAones : At Q a *ᵥ onesT = (14 : ℤ) • onesT := by
    change At Q a *ᵥ (fun _ => (1 : ℤ)) = _
    rw [hrow]
    ext i
    simp [onesT]
  have hJones : Jw *ᵥ onesT = (99 : ℤ) • onesT := by
    ext i
    simp only [mulVec, dotProduct, Jw, Matrix.of_apply, onesT, mul_one, wt_sum, Pi.smul_apply,
      smul_eq_mul]
  have hP2ones : P2 *ᵥ onesT = 0 := by
    rw [hP2, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hJones,
      hAones]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, onesT, Pi.zero_apply]
    norm_num
  set B1 : Matrix (Fin 32 ⊕ Fin 3) (Fin r ⊕ Unit) ℤ :=
    Matrix.fromCols B (Matrix.replicateCol Unit onesT) with hB1
  have hP2B : P2 * B = 0 := by
    rw [hP2]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hJB, hAB,
      smul_zero]
    module
  have hXB1 : P2 * B1 = 0 := by
    rw [hB1, mul_fromCols, hP2B]
    have h2 : P2 * Matrix.replicateCol Unit onesT = 0 := by
      ext i u
      have := congrFun hP2ones i
      simpa [Matrix.mul_apply, mulVec, dotProduct, onesT] using this
    rw [h2, fromCols_zero]
  have hB1eq : BW * CW * B1 = B1 := kernel_basis_mul' hBCW B1 hXB1
  set T : Matrix (Fin rW) (Fin r ⊕ Unit) ℤ := CW * B1 with hT
  have hB1T : B1 = BW * T := by rw [hT, ← Matrix.mul_assoc, hB1eq]
  -- 99 BW = B1 S
  set Y : Matrix (Fin 32 ⊕ Fin 3) (Fin rW) ℤ := (99 : ℤ) • BW - Jw * BW with hY
  have hXJ : (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * Jw =
      (11 : ℤ) • Jw := by
    rw [Matrix.sub_mul, hAJ, Matrix.smul_mul, Matrix.one_mul]
    module
  have hXY : (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * Y = 0 := by
    calc (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * Y
        = (99 : ℤ) • ((At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * BW)
          - ((At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * Jw) * BW := by
          rw [hY, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (99 : ℤ) • ((At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ)) * BW)
          - (11 : ℤ) • (Jw * BW) := by
          rw [hXJ, Matrix.smul_mul]
      _ = 0 := by
          rw [hJBW]
          module
  have hBCY : B * C * Y = Y := kernel_basis_mul' hBC Y hXY
  set S : Matrix (Fin r ⊕ Unit) (Fin rW) ℤ :=
    Matrix.fromRows (C * Y) (Matrix.of fun (_ : Unit) j => ∑ x, wt x * BW x j) with hS
  have hB1S : B1 * S = (99 : ℤ) • BW := by
    rw [hB1, hS, fromCols_mul_fromRows]
    have h1 : B * (C * Y) = Y := by rw [← Matrix.mul_assoc, hBCY]
    have h2 : Matrix.replicateCol Unit onesT * (Matrix.of fun (_ : Unit) j => ∑ x, wt x * BW x j)
        = Jw * BW := by
      ext x j
      simp [Matrix.mul_apply, Jw, onesT]
    rw [h1, h2, hY]
    abel
  have hTS : T * S = (99 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ) := by
    rw [hT, Matrix.mul_assoc, hB1S, Matrix.mul_smul, hCBW]
  -- ranks: rW = r + 1
  have h99ne : ((99 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ)).det ≠ 0 := by
    rw [det_smul, det_one]
    simp
  have hrW_le : rW ≤ r + 1 := by
    have h1 : (T * S).rank = rW := by
      rw [hTS, rank_of_det_ne_zero h99ne, Fintype.card_fin]
    calc rW = (T * S).rank := h1.symm
      _ ≤ T.rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r ⊕ Unit) := rank_le_card_width _
      _ = r + 1 := by simp
  have hBtD1 : Bᵀ * Dm * Matrix.replicateCol Unit onesT = 0 := by
    ext j u
    have h := congrFun (congrFun hJB (Sum.inl 0)) j
    simp only [Matrix.mul_apply, Jw, Matrix.of_apply, Matrix.zero_apply] at h
    rw [Matrix.mul_apply]
    simp only [Dm, Matrix.mul_diagonal, transpose_apply, Matrix.replicateCol_apply, onesT, mul_one,
      Matrix.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have h1DB : (Matrix.replicateCol Unit onesT)ᵀ * Dm * B = 0 := by
    have := congrArg Matrix.transpose hBtD1
    rwa [transpose_mul, transpose_mul, transpose_transpose, Dm_transpose, transpose_zero,
      ← Matrix.mul_assoc] at this
  have h1D1 : (Matrix.replicateCol Unit onesT)ᵀ * Dm * Matrix.replicateCol Unit onesT
      = Matrix.of fun (_ : Unit) (_ : Unit) => (99 : ℤ) := by
    ext u u'
    rw [Matrix.mul_apply]
    simp only [Dm, Matrix.mul_diagonal, transpose_apply, Matrix.replicateCol_apply, onesT, one_mul,
      mul_one, Matrix.of_apply, wt_sum]
  have hG1 : B1ᵀ * Dm * B1 = Matrix.fromBlocks ((3 : ℤ) • Gt B) 0 0
      (Matrix.of fun (_ : Unit) (_ : Unit) => (99 : ℤ)) := by
    rw [hB1, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, gram_eq B hdiv, hBtD1, h1DB,
      h1D1]
  have hdetG1 : (B1ᵀ * Dm * B1).det = 3 ^ r * (Gt B).det * 99 := by
    rw [hG1, det_fromBlocks_zero₂₁, det_smul,
      Matrix.det_unique (Matrix.of fun (_ : Unit) (_ : Unit) => (99 : ℤ)), Fintype.card_fin]
    simp
  have hrW_ge : r + 1 ≤ rW := by
    have hne : (B1ᵀ * Dm * B1).det ≠ 0 := by
      rw [hdetG1]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hpos.ne') (by norm_num)
    have h1 : (B1ᵀ * Dm * B1).rank = r + 1 := by
      rw [rank_of_det_ne_zero hne]
      simp
    calc r + 1 = (B1ᵀ * Dm * B1).rank := h1.symm
      _ ≤ B1.rank := rank_mul_le_right _ _
      _ = (BW * T).rank := by rw [← hB1T]
      _ ≤ T.rank := rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin rW) := rank_le_card_height _
      _ = rW := Fintype.card_fin _
  -- reindex and compare determinants: 99 · 3^r · det G̃ = det(T')² det(G_W)
  have hcard : Fintype.card (Fin r ⊕ Unit) = Fintype.card (Fin rW) := by
    simp
    omega
  set e : Fin r ⊕ Unit ≃ Fin rW := Fintype.equivOfCardEq hcard with he
  have hGram : B1ᵀ * Dm * B1 =
      (T.submatrix e id)ᵀ * (BWᵀ * Dm * BW).submatrix e e * T.submatrix e id := by
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id, hB1T,
      transpose_mul]
    simp only [Matrix.mul_assoc]
  have hkey : 11 * (9 * 3 ^ r) * (Gt B).det =
      (T.submatrix e id).det ^ 2 * (BWᵀ * Dm * BW).det := by
    have h := hdetG1
    rw [hGram, det_mul, det_mul, det_transpose, det_submatrix_equiv_self] at h
    linear_combination -h
  have hc0 : ¬ (11 : ℤ) ∣ 9 * 3 ^ r := by
    intro h
    have h2 : (11 : ℕ) ∣ 3 ^ (r + 2) := by
      have e2 : (3 : ℕ) ^ (r + 2) = 9 * 3 ^ r := by ring
      rw [e2]
      exact_mod_cast h
    have h3 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h2
    norm_num at h3
  exact int_mod3_eq_two_gen _ _ _ _ r hpos hdvd h11W (by positivity) hc0 hkey

end main

/-- **Proposition 2, matrix form.** No integer `Q` (32 × 32, symmetric), `a` (32 × 3) and Eisenstein
`M` (32 × 32, Hermitian) such that `Ã = [[Q, a], [3aᵀ, J₃ - I₃]]` satisfies `Ã 𝟙 = 14 𝟙`,
`Ã² + Ã = 12 I + 2 𝟙 wᵀ`, `M² + M = 12 I` and `M ≡ Q (mod 1 - ω)`. -/
theorem no_triangle_pair (Q : Matrix (Fin 32) (Fin 32) ℤ) (a : Matrix (Fin 32) (Fin 3) ℤ)
    (M : Matrix (Fin 32) (Fin 32) Eis) (hQs : Qᵀ = Q)
    (hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hsq : At Q a * At Q a + At Q a =
      (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw)
    (hMh : Mᴴ = M) (hMM : M * M + M = (12 : Eis) • (1 : Matrix (Fin 32) (Fin 32) Eis))
    (hQM : M.map Eis.rho = Q.map φ3) : False := by
  obtain ⟨r, B, C, hCB, hXB, hBC⟩ :=
    exists_kernel_basis' (At Q a - (3 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ))
  obtain ⟨hpos, hdvd, h1, hdiv⟩ := step5_tri hQs hrow hsq M hMh hMM hQM B C hCB hXB hBC
  have h2 := step4_tri hQs hrow hsq B C hCB hXB hBC hdiv hpos hdvd
  rw [h1] at h2
  exact absurd h2 (by decide)

end Tri

end C3
