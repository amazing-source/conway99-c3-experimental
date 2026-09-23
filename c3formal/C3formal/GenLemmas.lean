import C3formal.Main

/-!
# Size-generic versions of the step-5 core, of the Eisenstein side, and of the 11-adic lemma

Used for the fixed-triangle case (Proposition 2), where the free part has 32 orbits.
-/

open Matrix

namespace C3

section core

/-- Core of step 5 over `𝔽₃`, for any size `n`. -/
theorem core_F3_gen {n r r' : ℕ}
    (P : Matrix (Fin n) (Fin n) (ZMod 3))
    (B : Matrix (Fin n) (Fin r) (ZMod 3)) (C : Matrix (Fin r) (Fin n) (ZMod 3))
    (B' : Matrix (Fin n) (Fin r') (ZMod 3)) (C' : Matrix (Fin r') (Fin n) (ZMod 3))
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

section eisenstein

variable {n : ℕ}

/-- `N' = M + 4 I` in size `n`. -/
def NMn (M : Matrix (Fin n) (Fin n) Eis) : Matrix (Fin n) (Fin n) Eis :=
  M + (4 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis)

theorem M_step3n (M : Matrix (Fin n) (Fin n) Eis) (hMh : Mᴴ = M)
    (hMM : M * M + M = (12 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis))
    {r' : ℕ} (B' : Matrix (Fin n) (Fin r') Eis) (C' : Matrix (Fin r') (Fin n) Eis)
    (hCB' : C' * B' = 1) (hXB' : (M - (3 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis)) * B' = 0)
    (hBC' : ∀ v, (M - (3 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis)) *ᵥ v = 0 →
      B' *ᵥ (C' *ᵥ v) = v) :
    (NMn M)ᴴ = NMn M ∧ NMn M = B' * (C' * NMn M * C'ᴴ) * B'ᴴ ∧
      ((B'ᴴ * B') * (C' * NMn M * C'ᴴ)).det = 7 ^ r' := by
  have hMB : M * B' = (3 : Eis) • B' := by
    have h := hXB'
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hMM' : M * M = (12 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis) - M := by rw [← hMM]; abel
  have hXN : (M - (3 : Eis) • (1 : Matrix (Fin n) (Fin n) Eis)) * NMn M = 0 := by
    simp only [NMn, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hMM']
    module
  have hNB : NMn M * B' = (7 : Eis) • B' := by
    simp only [NMn, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hMB]
    module
  have h4 : star (4 : Eis) = 4 := by ext <;> simp
  have h7 : star (7 : Eis) = 7 := by ext <;> simp
  have hNh : (NMn M)ᴴ = NMn M := by
    simp only [NMn, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hMh, h4]
  obtain ⟨hN, hGK⟩ := gram_identities B' C' (NMn M) 7 h7 hCB'
    (kernel_basis_mul hBC' (NMn M) hXN) hNB hNh
  refine ⟨hNh, hN, ?_⟩
  rw [hGK, det_smul, det_one, mul_one, Fintype.card_fin]

theorem Msiden (M : Matrix (Fin n) (Fin n) Eis) {r' : ℕ} (B' : Matrix (Fin n) (Fin r') Eis)
    (C' : Matrix (Fin r') (Fin n) Eis) (hCB' : C' * B' = 1) (hNh : (NMn M)ᴴ = NMn M)
    (hdet' : ((B'ᴴ * B') * (C' * NMn M * C'ᴴ)).det = 7 ^ r') :
    Eis.rho (B'ᴴ * B').det = 1 := by
  obtain ⟨d, hdpos, hd⟩ := Eis.det_gram_pos B' C' hCB'
  have hK'h : (C' * NMn M * C'ᴴ)ᴴ = C' * NMn M * C'ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hNh, Matrix.mul_assoc]
  have hkstar : star (C' * NMn M * C'ᴴ).det = (C' * NMn M * C'ᴴ).det := by
    rw [← det_conjTranspose, hK'h]
  have hk := Eis.eq_intCast_of_star_eq hkstar
  rw [det_mul, hd, hk] at hdet'
  have hZ : d * (C' * NMn M * C'ᴴ).det.re = 7 ^ r' := by
    apply Eis.intCast_injective
    push_cast
    exact hdet'
  rw [hd, Eis.rho_intCast]
  exact int_mod3_eq_one d _ r' hdpos hZ

theorem NMn_map (Q : Matrix (Fin n) (Fin n) ℤ) (M : Matrix (Fin n) (Fin n) Eis)
    (hQM : M.map Eis.rho = Q.map φ3) :
    (NMn M).map Eis.rho = Q.map φ3 + 1 := by
  ext i j
  have hij := congrFun (congrFun hQM i) j
  simp only [Matrix.map_apply] at hij
  simp only [NMn, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, map_add, map_mul, hij]
  have h4 : Eis.rho 4 = 1 := by
    rw [Eis.rho_apply]
    decide
  split_ifs <;> simp [h4]

end eisenstein

section arith

theorem nat_mod3_eq_two_gen (D T G c0 r : ℕ) (hD : 0 < D) (hdvd : D ∣ 77 ^ r) (hG : ¬ 11 ∣ G)
    (hc0 : 0 < c0) (hc0' : ¬ 11 ∣ c0) (h : 11 * c0 * D = T ^ 2 * G) : (D : ZMod 3) = 2 := by
  have hp11 : Nat.Prime 11 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have := Fact.mk hp11
  have hGpos : 0 < G := Nat.pos_of_ne_zero (fun h0 => hG (by rw [h0]; exact dvd_zero 11))
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [h0] at h
      simp at h
      omega
    · exact h0
  obtain ⟨e, D0, hD0, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD.ne' 11 (by norm_num)
  obtain ⟨s, T0, hT0, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hTpos.ne' 11 (by norm_num)
  have hD0pos : 0 < D0 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hD)
  have hT0pos : 0 < T0 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hTpos)
  have v1 : padicValNat 11 (11 * c0 * (11 ^ e * D0)) = 1 + e := by
    rw [padicValNat.mul (by positivity : 11 * c0 ≠ 0) (by positivity : 11 ^ e * D0 ≠ 0),
      padicValNat.mul (by norm_num : (11 : ℕ) ≠ 0) hc0.ne', padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd hc0',
      padicValNat.mul (by positivity : (11 : ℕ) ^ e ≠ 0) hD0pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hD0, add_zero, add_zero]
  have v2 : padicValNat 11 ((11 ^ s * T0) ^ 2 * G) = 2 * s := by
    rw [padicValNat.mul (by positivity : (11 ^ s * T0) ^ 2 ≠ 0) hGpos.ne',
      padicValNat.pow (11 ^ s * T0) 2,
      padicValNat.mul (by positivity : (11 : ℕ) ^ s ≠ 0) hT0pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hT0, padicValNat.eq_zero_of_not_dvd hG, add_zero, add_zero]
  have hes : 1 + e = 2 * s := by rw [← v1, ← v2, h]
  have he : Odd e := ⟨s - 1, by omega⟩
  have hcop : Nat.Coprime D0 (11 ^ r) :=
    Nat.Coprime.pow_right r (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp11).mpr hD0))
  have hD0dvd : D0 ∣ 7 ^ r := by
    have h77 : (77 : ℕ) ^ r = 7 ^ r * 11 ^ r := by rw [← mul_pow]; norm_num
    have h1 : D0 ∣ 7 ^ r * 11 ^ r := by
      rw [← h77]
      exact dvd_trans (Dvd.intro_left _ rfl) hdvd
    exact hcop.dvd_of_dvd_mul_right h1
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hp7).mp hD0dvd
  push_cast
  have h11 : (11 : ZMod 3) = 2 := by decide
  have h7 : (7 : ZMod 3) = 1 := by decide
  rw [h11, h7, one_pow, mul_one, two_pow_odd e he]

theorem int_mod3_eq_two_gen (d t g c0 : ℤ) (r : ℕ) (hd : 0 < d) (hdvd : d ∣ 77 ^ r)
    (hg : ¬ (11 : ℤ) ∣ g) (hc0 : 0 < c0) (hc0' : ¬ (11 : ℤ) ∣ c0)
    (h : 11 * c0 * d = t ^ 2 * g) : (d : ZMod 3) = 2 := by
  have hD : 0 < d.natAbs := Int.natAbs_pos.mpr hd.ne'
  have hdvd' : d.natAbs ∣ 77 ^ r := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have hg' : ¬ 11 ∣ g.natAbs := fun h11 => hg (Int.ofNat_dvd_left.mpr h11)
  have hc0'' : ¬ 11 ∣ c0.natAbs := fun h11 => hc0' (Int.ofNat_dvd_left.mpr h11)
  have hc0pos : 0 < c0.natAbs := Int.natAbs_pos.mpr hc0.ne'
  have h' : 11 * c0.natAbs * d.natAbs = t.natAbs ^ 2 * g.natAbs := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have key := nat_mod3_eq_two_gen _ _ _ _ r hD hdvd' hg' hc0pos hc0'' h'
  have hdeq : ((d.natAbs : ℕ) : ℤ) = d := Int.natAbs_of_nonneg hd.le
  rw [← hdeq, Int.cast_natCast]
  exact key

end arith

end C3
