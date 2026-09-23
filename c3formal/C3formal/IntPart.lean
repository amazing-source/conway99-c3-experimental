import C3formal.Step5
import C3formal.Saturated
import C3formal.NumberTheory
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Module

/-!
# The integral side (steps 1, 3, 4): `det G ≡ 2 (mod 3)`

For a symmetric integer matrix `Q` with `Q 𝟙 = 14 𝟙` and `Q² + Q = 12 I + 6 J`, and an integral basis
`B` (with left inverse `C`) of `ker (Q - 3I)`:
* `Q_step3` : `N = B K Bᵀ` and `det (G K) = 77^r` (`N = 11(Q + 4I) - 6J`, `G = BᵀB`, `K = C N Cᵀ`);
* `Qside` : `det G ≡ 2 (mod 3)`, because `v₁₁(det G)` is odd: the lattice `ker (Q-3) ⊕ ℤ𝟙` has index
  prime to 11 in... more precisely `33 · det G = det(T)² · det G_W` with `11 ∤ det G_W`, where `G_W` is
  the Gram matrix of `ker ((Q-3)(Q-14))`.
-/

open Matrix

namespace C3

local notation "𝟙" => (1 : Matrix (Fin 33) (Fin 33) ℤ)

/-- The column of ones. -/
def ones : Fin 33 → ℤ := fun _ => 1

theorem J_transpose : (J 33)ᵀ = J 33 := by
  ext i j
  rfl

theorem J_mul_J : J 33 * J 33 = (33 : ℤ) • J 33 := by
  ext i j
  simp [Matrix.mul_apply, J]

theorem J_mulVec_ones : J 33 *ᵥ ones = (33 : ℤ) • ones := by
  ext i
  simp [mulVec, dotProduct, J, ones]

theorem Q_mul_J (Q : Matrix (Fin 33) (Fin 33) ℤ) (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14) :
    Q * J 33 = (14 : ℤ) • J 33 := by
  ext i j
  have h := congrFun hQ1 i
  simp only [mulVec, dotProduct, mul_one] at h
  simp only [Matrix.mul_apply, J, Matrix.of_apply, mul_one, Matrix.smul_apply, smul_eq_mul]
  exact h

theorem J_mul_Q (Q : Matrix (Fin 33) (Fin 33) ℤ) (hQs : Qᵀ = Q)
    (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14) : J 33 * Q = (14 : ℤ) • J 33 := by
  have h := congrArg Matrix.transpose (Q_mul_J Q hQ1)
  rw [transpose_mul, hQs, J_transpose, transpose_smul, J_transpose] at h
  exact h

theorem J_mul_eq_zero (Q : Matrix (Fin 33) (Fin 33) ℤ) (hQs : Qᵀ = Q)
    (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14) {r : ℕ} (B : Matrix (Fin 33) (Fin r) ℤ)
    (hQB : Q * B = (3 : ℤ) • B) : J 33 * B = 0 := by
  have h1 : J 33 * (Q * B) = (3 : ℤ) • (J 33 * B) := by rw [hQB, Matrix.mul_smul]
  rw [← Matrix.mul_assoc, J_mul_Q Q hQs hQ1, Matrix.smul_mul] at h1
  ext i j
  have h := congrFun (congrFun h1 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  simp only [Matrix.zero_apply]
  linarith

/-- Gram determinants of integer matrices with a left inverse are positive. -/
theorem det_gram_pos_int {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (C : Matrix (Fin r) (Fin n) ℤ)
    (hCB : C * B = 1) : 0 < (Bᵀ * B).det := by
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have := congrArg (fun w => C *ᵥ w) hxy
    simpa only [mulVec_mulVec, hCB, one_mulVec] using this
  have hpd := Matrix.PosDef.conjTranspose_mul_self B hinj
  rw [conjTranspose_eq_transpose_of_trivial] at hpd
  exact hpd.det_pos

/-- Steps 1 and 3 on the integral side. -/
theorem Q_step3 (Q : Matrix (Fin 33) (Fin 33) ℤ) (hQs : Qᵀ = Q)
    (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hQQ : Q * Q + Q = (12 : ℤ) • 𝟙 + (6 : ℤ) • J 33)
    {r : ℕ} (B : Matrix (Fin 33) (Fin r) ℤ) (C : Matrix (Fin r) (Fin 33) ℤ)
    (hCB : C * B = 1) (hXB : (Q - (3 : ℤ) • 𝟙) * B = 0)
    (hBC : ∀ v, (Q - (3 : ℤ) • 𝟙) *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v) :
    NQ Q = B * (C * NQ Q * Cᵀ) * Bᵀ ∧ ((Bᵀ * B) * (C * NQ Q * Cᵀ)).det = 77 ^ r := by
  have hQJ := Q_mul_J Q hQ1
  have hQQ' : Q * Q = (12 : ℤ) • 𝟙 + (6 : ℤ) • J 33 - Q := by rw [← hQQ]; abel
  have hQB : Q * B = (3 : ℤ) • B := by
    have h := hXB
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hJB : J 33 * B = 0 := J_mul_eq_zero Q hQs hQ1 B hQB
  have hXN : (Q - (3 : ℤ) • 𝟙) * NQ Q = 0 := by
    simp only [NQ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hQQ', hQJ]
    module
  have hNB : NQ Q * B = (77 : ℤ) • B := by
    simp only [NQ, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hQB, hJB,
      smul_zero]
    module
  have hNt : (NQ Q)ᴴ = NQ Q := by
    rw [conjTranspose_eq_transpose_of_trivial]
    simp only [NQ, transpose_sub, transpose_smul, transpose_add, transpose_one, hQs, J_transpose]
  obtain ⟨hN, hGK⟩ := gram_identities B C (NQ Q) (77 : ℤ) (by simp) hCB
    (kernel_basis_mul hBC (NQ Q) hXN) hNB hNt
  simp only [conjTranspose_eq_transpose_of_trivial] at hN hGK
  refine ⟨hN, ?_⟩
  rw [hGK, det_smul, det_one, mul_one, Fintype.card_fin]

/-- **Step 4.** `det G ≡ 2 (mod 3)`. -/
theorem Qside (Q : Matrix (Fin 33) (Fin 33) ℤ) (hQs : Qᵀ = Q)
    (hQ1 : Q *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hQQ : Q * Q + Q = (12 : ℤ) • 𝟙 + (6 : ℤ) • J 33)
    {r : ℕ} (B : Matrix (Fin 33) (Fin r) ℤ) (C : Matrix (Fin r) (Fin 33) ℤ)
    (hCB : C * B = 1) (hXB : (Q - (3 : ℤ) • 𝟙) * B = 0)
    (hBC : ∀ v, (Q - (3 : ℤ) • 𝟙) *ᵥ v = 0 → B *ᵥ (C *ᵥ v) = v)
    (hdvd : (Bᵀ * B).det ∣ 77 ^ r) :
    ((Bᵀ * B).det : ZMod 3) = 2 := by
  have hQJ := Q_mul_J Q hQ1
  have hJQ := J_mul_Q Q hQs hQ1
  have hJJ := J_mul_J
  have hQQ' : Q * Q = (12 : ℤ) • 𝟙 + (6 : ℤ) • J 33 - Q := by rw [← hQQ]; abel
  have hQB : Q * B = (3 : ℤ) • B := by
    have h := hXB
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hJB : J 33 * B = 0 := J_mul_eq_zero Q hQs hQ1 B hQB
  -- the lattice W = ker ((Q - 3)(Q - 14))
  have hP2' : (Q - (3 : ℤ) • 𝟙) * (Q - (14 : ℤ) • 𝟙) = (6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hQQ']
    module
  obtain ⟨rW, BW, CW, hCBW, hXBW, hBCW⟩ :=
    exists_kernel_basis ((Q - (3 : ℤ) • 𝟙) * (Q - (14 : ℤ) • 𝟙))
  rw [hP2'] at hXBW hBCW
  have hJBW : J 33 * BW = (3 : ℤ) • ((Q - (3 : ℤ) • 𝟙) * BW) := by
    have h0 := hXBW
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h0
    ext i j
    have h := congrFun (congrFun h0 i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at h
    simp only [Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.one_mul, smul_eq_mul]
    linarith
  set NW : Matrix (Fin 33) (Fin 33) ℤ := (3 : ℤ) • (Q + (4 : ℤ) • 𝟙) - J 33 with hNW
  have hXNW : ((6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙) * NW = 0 := by
    rw [hNW]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hJQ, hJJ, hQQ', hQJ]
    module
  have hNWB : NW * BW = (21 : ℤ) • BW := by
    rw [hNW]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, hJBW]
    module
  have hNWt : NWᴴ = NW := by
    rw [conjTranspose_eq_transpose_of_trivial, hNW]
    simp only [transpose_sub, transpose_smul, transpose_add, transpose_one, hQs, J_transpose]
  obtain ⟨-, hGKW⟩ := gram_identities BW CW NW (21 : ℤ) (by simp) hCBW
    (kernel_basis_mul hBCW NW hXNW) hNWB hNWt
  simp only [conjTranspose_eq_transpose_of_trivial] at hGKW
  have hdetW : (BWᵀ * BW).det * (CW * NW * CWᵀ).det = 21 ^ rW := by
    rw [← det_mul, hGKW, det_smul, det_one, mul_one, Fintype.card_fin]
  have h11W : ¬ (11 : ℤ) ∣ (BWᵀ * BW).det := by
    intro h11
    have h1 : (11 : ℤ) ∣ 21 ^ rW := dvd_trans h11 (Dvd.intro _ hdetW)
    have h2 : (11 : ℕ) ∣ 21 ^ rW := by exact_mod_cast h1
    have h3 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h2
    norm_num at h3
  -- B1 = [B | 𝟙]
  have hQones : Q *ᵥ ones = (14 : ℤ) • ones := by
    change Q *ᵥ (fun _ => (1 : ℤ)) = _
    rw [hQ1]
    ext i
    simp [ones]
  have hP2ones : ((6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙) *ᵥ ones = 0 := by
    rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
      J_mulVec_ones, hQones]
    ext i
    simp [ones]
  set B1 : Matrix (Fin 33) (Fin r ⊕ Unit) ℤ := Matrix.fromCols B (Matrix.replicateCol Unit ones)
    with hB1
  have hP2B : ((6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙) * B = 0 := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hJB, hQB, smul_zero]
    module
  have hXB1 : ((6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙) * B1 = 0 := by
    rw [hB1, mul_fromCols, hP2B]
    have h2 : ((6 : ℤ) • J 33 - (18 : ℤ) • Q + (54 : ℤ) • 𝟙) * Matrix.replicateCol Unit ones = 0 := by
      ext i u
      have := congrFun hP2ones i
      simpa [Matrix.mul_apply, mulVec, dotProduct, ones] using this
    rw [h2, fromCols_zero]
  have hB1eq : BW * CW * B1 = B1 := kernel_basis_mul hBCW B1 hXB1
  set T : Matrix (Fin rW) (Fin r ⊕ Unit) ℤ := CW * B1 with hT
  have hB1T : B1 = BW * T := by rw [hT, ← Matrix.mul_assoc, hB1eq]
  -- 33 BW = B1 S
  set Y : Matrix (Fin 33) (Fin rW) ℤ := (33 : ℤ) • BW - J 33 * BW with hY
  have hXJ : (Q - (3 : ℤ) • 𝟙) * J 33 = (11 : ℤ) • J 33 := by
    rw [Matrix.sub_mul, hQJ, Matrix.smul_mul, Matrix.one_mul]
    module
  have hXY : (Q - (3 : ℤ) • 𝟙) * Y = 0 := by
    calc (Q - (3 : ℤ) • 𝟙) * Y
        = (33 : ℤ) • ((Q - (3 : ℤ) • 𝟙) * BW) - ((Q - (3 : ℤ) • 𝟙) * J 33) * BW := by
          rw [hY, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (33 : ℤ) • ((Q - (3 : ℤ) • 𝟙) * BW) - (11 : ℤ) • (J 33 * BW) := by
          rw [hXJ, Matrix.smul_mul]
      _ = 0 := by
          rw [hJBW]
          module
  have hBCY : B * C * Y = Y := kernel_basis_mul hBC Y hXY
  set S : Matrix (Fin r ⊕ Unit) (Fin rW) ℤ :=
    Matrix.fromRows (C * Y) (Matrix.of fun (_ : Unit) j => ∑ i, BW i j) with hS
  have hB1S : B1 * S = (33 : ℤ) • BW := by
    rw [hB1, hS, fromCols_mul_fromRows]
    have h1 : B * (C * Y) = Y := by rw [← Matrix.mul_assoc, hBCY]
    have h2 : Matrix.replicateCol Unit ones * (Matrix.of fun (_ : Unit) j => ∑ i, BW i j)
        = J 33 * BW := by
      ext a j
      simp [Matrix.mul_apply, J, ones]
    rw [h1, h2, hY]
    abel
  have hTS : T * S = (33 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ) := by
    rw [hT, Matrix.mul_assoc, hB1S, Matrix.mul_smul, hCBW]
  -- ranks: rW = r + 1
  have h33ne : ((33 : ℤ) • (1 : Matrix (Fin rW) (Fin rW) ℤ)).det ≠ 0 := by
    rw [det_smul, det_one]
    simp
  have hrW_le : rW ≤ r + 1 := by
    have h1 : (T * S).rank = rW := by
      rw [hTS, rank_of_det_ne_zero h33ne, Fintype.card_fin]
    calc rW = (T * S).rank := h1.symm
      _ ≤ T.rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r ⊕ Unit) := rank_le_card_width _
      _ = r + 1 := by simp
  have hBt1 : Bᵀ * Matrix.replicateCol Unit ones = 0 := by
    ext j u
    have := congrFun (congrFun hJB 0) j
    simpa [Matrix.mul_apply, J, ones] using this
  have ht1B : (Matrix.replicateCol Unit ones)ᵀ * B = 0 := by
    have := congrArg Matrix.transpose hBt1
    rwa [transpose_mul, transpose_transpose, transpose_zero] at this
  have h11 : (Matrix.replicateCol Unit ones)ᵀ * Matrix.replicateCol Unit ones
      = Matrix.of fun (_ : Unit) (_ : Unit) => (33 : ℤ) := by
    ext a b
    simp [Matrix.mul_apply, ones]
  have hG1 : B1ᵀ * B1 = Matrix.fromBlocks (Bᵀ * B) 0 0 (Matrix.of fun (_ : Unit) (_ : Unit) => (33 : ℤ)) := by
    rw [hB1, transpose_fromCols, fromRows_mul_fromCols, hBt1, ht1B, h11]
  have hdetG1 : (B1ᵀ * B1).det = 33 * (Bᵀ * B).det := by
    rw [hG1, det_fromBlocks_zero₂₁,
      Matrix.det_unique (Matrix.of fun (_ : Unit) (_ : Unit) => (33 : ℤ))]
    simp [mul_comm]
  have hd_pos := det_gram_pos_int B C hCB
  have hrW_ge : r + 1 ≤ rW := by
    have hne : (B1ᵀ * B1).det ≠ 0 := by
      rw [hdetG1]
      exact mul_ne_zero (by norm_num) hd_pos.ne'
    have h1 : (B1ᵀ * B1).rank = r + 1 := by
      rw [rank_of_det_ne_zero hne]
      simp
    calc r + 1 = (B1ᵀ * B1).rank := h1.symm
      _ ≤ B1.rank := rank_mul_le_right _ _
      _ = (BW * T).rank := by rw [← hB1T]
      _ ≤ T.rank := rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin rW) := rank_le_card_height _
      _ = rW := Fintype.card_fin _
  -- reindex and compare determinants: 33 d = det(T')² det(G_W)
  have hcard : Fintype.card (Fin r ⊕ Unit) = Fintype.card (Fin rW) := by
    simp
    omega
  set e : Fin r ⊕ Unit ≃ Fin rW := Fintype.equivOfCardEq hcard with he
  have hGram : B1ᵀ * B1 = (T.submatrix e id)ᵀ * (BWᵀ * BW).submatrix e e * T.submatrix e id := by
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id, hB1T,
      transpose_mul]
    simp only [Matrix.mul_assoc]
  have hkey : 33 * (Bᵀ * B).det = (T.submatrix e id).det ^ 2 * (BWᵀ * BW).det := by
    rw [← hdetG1, hGram, det_mul, det_mul, det_transpose, det_submatrix_equiv_self]
    ring
  exact int_mod3_eq_two _ _ _ r hd_pos hdvd h11W hkey

end C3
