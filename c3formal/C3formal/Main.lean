import C3formal.IntPart
import C3formal.EisEuclid
import C3formal.EisComplex

/-!
# The central (matrix) theorem

**Theorem (`C3.no_pair`).** There is no pair `(Q, M)` with
* `Q` a symmetric `33 × 33` integer matrix, `Q 𝟙 = 14 𝟙`, `Q² + Q = 12 I + 6 J`,
* `M` a Hermitian `33 × 33` matrix over the Eisenstein integers, `M² + M = 12 I`,
* `M ≡ Q (mod 1 - ω)` entrywise (i.e. `ρ(M) = Q mod 3`).

A fixed-point-free automorphism of order 3 of a strongly regular graph `srg(99,14,1,2)` produces
such a pair (`Q = A(1)`, `M = A(ω)`); see `pdf/preuve_c3.pdf`, Lemma 4.
-/

open Matrix

namespace C3

local notation "𝟙E" => (1 : Matrix (Fin 33) (Fin 33) Eis)

/-- Steps 1 and 3 on the Eisenstein side, plus Hermitian symmetry of `N'`. -/
theorem M_step3 (M : Matrix (Fin 33) (Fin 33) Eis) (hMh : Mᴴ = M)
    (hMM : M * M + M = (12 : Eis) • 𝟙E)
    {r' : ℕ} (B' : Matrix (Fin 33) (Fin r') Eis) (C' : Matrix (Fin r') (Fin 33) Eis)
    (hCB' : C' * B' = 1) (hXB' : (M - (3 : Eis) • 𝟙E) * B' = 0)
    (hBC' : ∀ v, (M - (3 : Eis) • 𝟙E) *ᵥ v = 0 → B' *ᵥ (C' *ᵥ v) = v) :
    (NM M)ᴴ = NM M ∧ NM M = B' * (C' * NM M * C'ᴴ) * B'ᴴ ∧
      ((B'ᴴ * B') * (C' * NM M * C'ᴴ)).det = 7 ^ r' := by
  have hMB : M * B' = (3 : Eis) • B' := by
    have h := hXB'
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hMM' : M * M = (12 : Eis) • 𝟙E - M := by rw [← hMM]; abel
  have hXN : (M - (3 : Eis) • 𝟙E) * NM M = 0 := by
    simp only [NM, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hMM']
    module
  have hNB : NM M * B' = (7 : Eis) • B' := by
    simp only [NM, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hMB]
    module
  have h4 : star (4 : Eis) = 4 := by ext <;> simp
  have h7 : star (7 : Eis) = 7 := by ext <;> simp
  have hNh : (NM M)ᴴ = NM M := by
    simp only [NM, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hMh, h4]
  obtain ⟨hN, hGK⟩ := gram_identities B' C' (NM M) 7 h7 hCB'
    (kernel_basis_mul hBC' (NM M) hXN) hNB hNh
  refine ⟨hNh, hN, ?_⟩
  rw [hGK, det_smul, det_one, mul_one, Fintype.card_fin]

/-- The Eisenstein discriminant is `≡ 1 (mod 3)`: it is a positive divisor of `7^r'`. -/
theorem Mside (M : Matrix (Fin 33) (Fin 33) Eis) {r' : ℕ} (B' : Matrix (Fin 33) (Fin r') Eis)
    (C' : Matrix (Fin r') (Fin 33) Eis) (hCB' : C' * B' = 1) (hNh : (NM M)ᴴ = NM M)
    (hdet' : ((B'ᴴ * B') * (C' * NM M * C'ᴴ)).det = 7 ^ r') :
    Eis.rho (B'ᴴ * B').det = 1 := by
  obtain ⟨d, hdpos, hd⟩ := Eis.det_gram_pos B' C' hCB'
  have hK'h : (C' * NM M * C'ᴴ)ᴴ = C' * NM M * C'ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hNh, Matrix.mul_assoc]
  have hkstar : star (C' * NM M * C'ᴴ).det = (C' * NM M * C'ᴴ).det := by
    rw [← det_conjTranspose, hK'h]
  have hk := Eis.eq_intCast_of_star_eq hkstar
  rw [det_mul, hd, hk] at hdet'
  have hZ : d * (C' * NM M * C'ᴴ).det.re = 7 ^ r' := by
    apply Eis.intCast_injective
    push_cast
    exact hdet'
  rw [hd, Eis.rho_intCast]
  exact int_mod3_eq_one d _ r' hdpos hZ

/-- **The central theorem.** -/
theorem no_pair (Q : Matrix (Fin 33) (Fin 33) ℤ) (M : Matrix (Fin 33) (Fin 33) Eis)
    (hQs : Qᵀ = Q) (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hQQ : Q * Q + Q = (12 : ℤ) • (1 : Matrix (Fin 33) (Fin 33) ℤ) + (6 : ℤ) • J 33)
    (hMh : Mᴴ = M) (hMM : M * M + M = (12 : Eis) • 𝟙E)
    (hQM : M.map Eis.rho = Q.map φ3) : False := by
  obtain ⟨r, B, C, hCB, hXB, hBC⟩ :=
    exists_kernel_basis (Q - (3 : ℤ) • (1 : Matrix (Fin 33) (Fin 33) ℤ))
  obtain ⟨r', B', C', hCB', hXB', hBC'⟩ := exists_kernel_basis (M - (3 : Eis) • 𝟙E)
  obtain ⟨hN, hdet⟩ := Q_step3 Q hQs hQ1 hQQ B C hCB hXB hBC
  obtain ⟨hNh', hN', hdet'⟩ := M_step3 M hMh hMM B' C' hCB' hXB' hBC'
  -- step 5: the two discriminants agree modulo 3
  obtain ⟨-, hcong⟩ := step5 Q M hQM B C B' C' hN hdet hN' hdet'
  -- step 4: the integral one is 2, the Eisenstein one is 1
  have hdvd : (Bᵀ * B).det ∣ 77 ^ r := Dvd.intro _ (by rw [← det_mul]; exact hdet)
  have h2 := Qside Q hQs hQ1 hQQ B C hCB hXB hBC hdvd
  have h1 := Mside M B' C' hCB' hNh' hdet'
  rw [h2, h1] at hcong
  exact absurd hcong (by decide)

end C3
