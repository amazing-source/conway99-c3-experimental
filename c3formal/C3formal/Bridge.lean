import C3formal.Main
import Mathlib.Tactic.FinCases

/-!
# Lemma 4: from a shift-invariant adjacency matrix to the pair `(Q, M)`

Vertices are labelled `(U, b) ∈ Fin 33 × ZMod 3` and the automorphism is the shift
`(U, b) ↦ (U, b + 1)`. For an integer matrix `A` with `Aᵀ = A`, `A 𝟙 = 14 𝟙`, `A² + A = 12 I + 2 J`
which is invariant under the shift, the matrices
`Q U V = ∑_b A (U,0) (V,b)` and `M U V = ∑_b ω^b A (U,0) (V,b)`
satisfy all hypotheses of `C3.no_pair`; hence no such `A` exists.
-/

open Matrix

namespace C3

/-- `ω ^ b` for `b : ZMod 3`. -/
def wpow (b : ZMod 3) : Eis := Eis.w ^ b.val

theorem wpow_add (b c : ZMod 3) : wpow (b + c) = wpow b * wpow c := by
  fin_cases b <;> fin_cases c <;> decide

theorem star_wpow (b : ZMod 3) : star (wpow b) = wpow (-b) := by
  fin_cases b <;> decide

theorem rho_wpow (b : ZMod 3) : Eis.rho (wpow b) = 1 := by
  fin_cases b <;> decide

theorem sum_zmod3 {β : Type*} [AddCommMonoid β] (f : ZMod 3 → β) :
    ∑ b : ZMod 3, f b = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

theorem sum_wpow : ∑ b : ZMod 3, wpow b = 0 := by
  rw [sum_zmod3]
  decide

section bridge

variable (A : Matrix (Fin 33 × ZMod 3) (Fin 33 × ZMod 3) ℤ)

theorem shift_k (h : ∀ U V b c, A (U, b + 1) (V, c + 1) = A (U, b) (V, c)) :
    ∀ U V b c k, A (U, b + k) (V, c + k) = A (U, b) (V, c) := by
  intro U V b c k
  have hn : ∀ n : ℕ, ∀ b c, A (U, b + n) (V, c + n) = A (U, b) (V, c) := by
    intro n
    induction n with
    | zero => intro b c; simp
    | succ n ih =>
      intro b c
      rw [Nat.cast_succ, ← add_assoc, ← add_assoc, h, ih]
  have := hn k.val b c
  rwa [ZMod.natCast_zmod_val] at this

/-- The convolution identity behind `Φ(A²) = Φ(A)²`. -/
theorem conv {R : Type*} [CommRing R]
    (hk : ∀ U V b c k, A (U, b + k) (V, c + k) = A (U, b) (V, c))
    (φ : ZMod 3 → R) (U V : Fin 33) :
    ∑ d : ZMod 3, ((A * A) (U, 0) (V, d) : R) * φ d =
      ∑ W : Fin 33, ∑ b : ZMod 3, ∑ c : ZMod 3,
        (A (U, 0) (W, b) : R) * (A (W, 0) (V, c) : R) * φ (b + c) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Equiv.sum_comp (Equiv.addLeft b)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Equiv.coe_addLeft]
  have hc := hk W V 0 c b
  rw [zero_add, add_comm c b] at hc
  rw [hc]

theorem no_shift_invariant (hAs : Aᵀ = A) (hA1 : A *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hAA : A * A + A =
      (12 : ℤ) • (1 : Matrix (Fin 33 × ZMod 3) (Fin 33 × ZMod 3) ℤ) + (2 : ℤ) • Matrix.of (fun _ _ => 1))
    (hshift : ∀ U V b c, A (U, b + 1) (V, c + 1) = A (U, b) (V, c)) : False := by
  have hk := shift_k A hshift
  have hsym : ∀ x y, A y x = A x y := fun x y => congrFun (congrFun hAs x) y
  -- entries of `A² + A`
  have hAAe : ∀ U V d, (A * A) (U, 0) (V, d) + A (U, 0) (V, d) =
      12 * (if U = V ∧ (0 : ZMod 3) = d then 1 else 0) + 2 := by
    intro U V d
    have h := congrFun (congrFun hAA (U, 0)) (V, d)
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, smul_eq_mul, mul_one] at h
    rw [h]
    simp only [Prod.mk.injEq]
  -- the sums over an orbit
  have hsumAA : ∀ (R : Type) [CommRing R] (φ : ZMod 3 → R) (U V : Fin 33),
      ∑ d : ZMod 3, (((A * A) (U, 0) (V, d) : ℤ) : R) * φ d + ∑ d : ZMod 3, ((A (U, 0) (V, d) : ℤ) : R) * φ d
        = 12 * (if U = V then φ 0 else 0) + 2 * ∑ d : ZMod 3, φ d := by
    intro R _ φ U V
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_mul, ← Int.cast_add, hAAe]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    congr 1
    by_cases hUV : U = V
    · simp [hUV, Finset.sum_ite_eq]
    · simp [hUV]
  -- the pair (Q, M)
  set Q : Matrix (Fin 33) (Fin 33) ℤ := Matrix.of fun U V => ∑ b : ZMod 3, A (U, 0) (V, b) with hQ
  set M : Matrix (Fin 33) (Fin 33) Eis :=
    Matrix.of fun U V => ∑ b : ZMod 3, ((A (U, 0) (V, b) : ℤ) : Eis) * wpow b with hM
  -- reversal of an orbit sum
  have hrev : ∀ U V (b : ZMod 3), A (V, 0) (U, b) = A (U, 0) (V, -b) := by
    intro U V b
    rw [hsym]
    have := hk U V 0 (-b) b
    rwa [zero_add, neg_add_cancel] at this
  apply no_pair Q M
  · -- Q symmetric
    ext U V
    simp only [transpose_apply, hQ, Matrix.of_apply]
    simp_rw [hrev U V]
    exact Equiv.sum_comp (Equiv.neg (ZMod 3)) (fun c => A (U, 0) (V, c))
  · -- row sums
    ext U
    have := congrFun hA1 (U, 0)
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, mul_one] at this
    simpa [mulVec, dotProduct, hQ, Matrix.of_apply] using this
  · -- Q² + Q = 12 I + 6 J
    refine Matrix.ext fun U V => ?_
    have h := hsumAA ℤ (fun _ => 1) U V
    rw [conv A hk] at h
    have hsum3 : ∑ _d : ZMod 3, (1 : ℤ) = 3 := by simp
    simp only [Int.cast_id, mul_one, hsum3] at h
    have hQQe : (Q * Q) U V =
        ∑ W : Fin 33, ∑ b : ZMod 3, ∑ c : ZMod 3, A (U, 0) (W, b) * A (W, 0) (V, c) := by
      simp only [Matrix.mul_apply, hQ, Matrix.of_apply, Finset.sum_mul_sum]
    rw [Matrix.add_apply, hQQe]
    simp only [hQ, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, J,
      smul_eq_mul]
    rw [h]
    split_ifs <;> norm_num
  · -- M Hermitian
    refine Matrix.ext fun U V => ?_
    simp only [conjTranspose_apply, hM, Matrix.of_apply, star_sum, star_mul', star_intCast,
      star_wpow]
    simp_rw [hrev U V]
    exact Equiv.sum_comp (Equiv.neg (ZMod 3)) (fun c => ((A (U, 0) (V, c) : ℤ) : Eis) * wpow c)
  · -- M² + M = 12 I
    refine Matrix.ext fun U V => ?_
    have h := hsumAA Eis wpow U V
    rw [conv A hk, sum_wpow] at h
    simp only [wpow_add] at h
    have hMMe : (M * M) U V = ∑ W : Fin 33, ∑ b : ZMod 3, ∑ c : ZMod 3,
        ((A (U, 0) (W, b) : ℤ) : Eis) * ((A (W, 0) (V, c) : ℤ) : Eis) * (wpow b * wpow c) := by
      simp only [Matrix.mul_apply, hM, Matrix.of_apply, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [Matrix.add_apply, hMMe]
    simp only [hM, Matrix.of_apply]
    rw [h]
    by_cases hUV : U = V
    · simp [hUV, wpow, Matrix.smul_apply]
    · simp [hUV, Matrix.smul_apply]
  · -- M ≡ Q (mod 1 - ω)
    refine Matrix.ext fun U V => ?_
    simp [hM, hQ, map_sum, rho_wpow]

end bridge

end C3
