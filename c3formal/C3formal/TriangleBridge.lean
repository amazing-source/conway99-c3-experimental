import C3formal.TriangleStep4
import C3formal.Bridge

/-!
# Lemma 4, fixed-triangle version: from an invariant adjacency matrix to `(Q, a, M)`

Vertices are labelled by `(Fin 32 × ZMod 3) ⊕ Fin 3`: the automorphism is the shift
`(U, b) ↦ (U, b + 1)` on the 32 free orbits and fixes the three points of `Fin 3`, which form a
triangle. For an integer matrix `A` with `Aᵀ = A`, `A 𝟙 = 14 𝟙`, `A² + A = 12 I + 2 J`, invariant
under the automorphism, the matrices

* `Q U V = ∑_b A (U,0) (V,b)`, `a U t = A (U,0) t`, `M U V = ∑_b ω^b A (U,0) (V,b)`

satisfy the hypotheses of `C3.Tri.no_triangle_pair`; hence no such `A` exists.

Method: with the orbit indicator `E` and the selection `R` of representatives (`R E = I`), one has
`A E = E Ã`, so `Ã² + Ã = R (A² + A) E = 12 I + 2 R J E = 12 I + 2 𝟙 wᵀ`. Likewise with the twisted
indicator `E_ω` (which vanishes on fixed points): `A E_ω = E_ω M` and `M² + M = 12 I`.
-/

open Matrix

namespace C3

namespace Tri

/-- Invariance under `+1` gives invariance under `+k`. -/
theorem shift_gen {β : Type*} (f : ZMod 3 → ZMod 3 → β) (h : ∀ b c, f (b + 1) (c + 1) = f b c)
    (b c k : ZMod 3) : f (b + k) (c + k) = f b c := by
  have hn : ∀ n : ℕ, ∀ b c, f (b + n) (c + n) = f b c := by
    intro n
    induction n with
    | zero => intro b c; simp
    | succ n ih =>
      intro b c
      rw [Nat.cast_succ, ← add_assoc, ← add_assoc, h, ih]
  have := hn k.val b c
  rwa [ZMod.natCast_zmod_val] at this

/-- The orbit of a vertex. -/
def orb : (Fin 32 × ZMod 3) ⊕ Fin 3 → Fin 32 ⊕ Fin 3 := Sum.map Prod.fst id

/-- The chosen representative of an orbit. -/
def rep : Fin 32 ⊕ Fin 3 → (Fin 32 × ZMod 3) ⊕ Fin 3 := Sum.map (fun U => (U, 0)) id

theorem orb_rep (o : Fin 32 ⊕ Fin 3) : orb (rep o) = o := by
  rcases o with U | t <;> rfl

/-- Orbit indicator matrix `E`. -/
def Em : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ :=
  Matrix.of fun x o => if orb x = o then 1 else 0

/-- Selection `R` of the representatives. -/
def Rm : Matrix (Fin 32 ⊕ Fin 3) ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ :=
  Matrix.of fun o x => if x = rep o then 1 else 0

theorem Rm_mul {κ : Type*} (N : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) κ ℤ) (o : Fin 32 ⊕ Fin 3)
    (k : κ) : (Rm * N) o k = N (rep o) k := by
  simp [Rm, Matrix.mul_apply]

theorem Em_mul {κ : Type*} (N : Matrix (Fin 32 ⊕ Fin 3) κ ℤ) (x : (Fin 32 × ZMod 3) ⊕ Fin 3)
    (k : κ) : (Em * N) x k = N (orb x) k := by
  simp [Em, Matrix.mul_apply]

theorem mul_Em_inl {κ : Type*} (N : Matrix κ ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ) (k : κ) (V : Fin 32) :
    (N * Em) k (Sum.inl V) = ∑ c : ZMod 3, N k (Sum.inl (V, c)) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Em, orb]

theorem mul_Em_inr {κ : Type*} (N : Matrix κ ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ) (k : κ) (t : Fin 3) :
    (N * Em) k (Sum.inr t) = N k (Sum.inr t) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [Em, orb]

/-- Twisted indicator `E_ω`: `ω^b` at `(U, b)`, zero on the fixed points. -/
def Ew : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) (Fin 32) Eis :=
  Matrix.of fun x V =>
    Sum.elim (fun p : Fin 32 × ZMod 3 => if p.1 = V then wpow p.2 else 0) (fun _ => 0) x

/-- Selection of the representatives `(U, 0)` of the free orbits. -/
def Rw : Matrix (Fin 32) ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis :=
  Matrix.of fun U x => if x = Sum.inl (U, 0) then 1 else 0

theorem Rw_mul {κ : Type*} (N : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) κ Eis) (U : Fin 32) (k : κ) :
    (Rw * N) U k = N (Sum.inl (U, 0)) k := by
  simp [Rw, Matrix.mul_apply]

theorem mul_Ew {κ : Type*} (N : Matrix κ ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis) (k : κ) (V : Fin 32) :
    (N * Ew) k V = ∑ c : ZMod 3, N k (Sum.inl (V, c)) * wpow c := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Ew]

theorem Ew_mul_inl {κ : Type*} (N : Matrix (Fin 32) κ Eis) (U : Fin 32) (b : ZMod 3) (k : κ) :
    (Ew * N) (Sum.inl (U, b)) k = wpow b * N U k := by
  simp [Ew, Matrix.mul_apply]

theorem Ew_mul_inr {κ : Type*} (N : Matrix (Fin 32) κ Eis) (t : Fin 3) (k : κ) :
    (Ew * N) (Sum.inr t) k = 0 := by
  simp [Ew, Matrix.mul_apply]

/-- **Lemma 4, fixed-triangle version.** -/
theorem no_tri_shift_invariant
    (A : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ)
    (hAs : Aᵀ = A) (hA1 : A *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14)
    (hAA : A * A + A = (12 : ℤ) • (1 : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3)
      ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ) + (2 : ℤ) • Matrix.of (fun _ _ => 1))
    (hshift : ∀ U V b c,
      A (Sum.inl (U, b + 1)) (Sum.inl (V, c + 1)) = A (Sum.inl (U, b)) (Sum.inl (V, c)))
    (hshift' : ∀ U b t, A (Sum.inl (U, b + 1)) (Sum.inr t) = A (Sum.inl (U, b)) (Sum.inr t))
    (htri : ∀ s t, A (Sum.inr s) (Sum.inr t) = if s = t then 0 else 1) : False := by
  have hsym : ∀ x y, A y x = A x y := fun x y => congrFun (congrFun hAs x) y
  have hk : ∀ U V b c k,
      A (Sum.inl (U, b + k)) (Sum.inl (V, c + k)) = A (Sum.inl (U, b)) (Sum.inl (V, c)) :=
    fun U V b c k => shift_gen (fun b c => A (Sum.inl (U, b)) (Sum.inl (V, c))) (hshift U V) b c k
  have hk' : ∀ U b t k, A (Sum.inl (U, b + k)) (Sum.inr t) = A (Sum.inl (U, b)) (Sum.inr t) :=
    fun U b t k =>
      shift_gen (fun b _ => A (Sum.inl (U, b)) (Sum.inr t)) (fun b _ => hshift' U b t) b 0 k
  obtain ⟨J, hJ⟩ : ∃ J : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ,
      J = Matrix.of fun _ _ => 1 := ⟨_, rfl⟩
  rw [← hJ] at hAA
  -- the data (Q, a, M)
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 32) (Fin 32) ℤ,
      Q = Matrix.of fun U V => ∑ b : ZMod 3, A (Sum.inl (U, 0)) (Sum.inl (V, b)) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Matrix (Fin 32) (Fin 3) ℤ,
      a = Matrix.of fun U t => A (Sum.inl (U, 0)) (Sum.inr t) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 32) (Fin 32) Eis,
      M = Matrix.of fun U V =>
        ∑ b : ZMod 3, ((A (Sum.inl (U, 0)) (Sum.inl (V, b)) : ℤ) : Eis) * wpow b := ⟨_, rfl⟩
  -- A E = E Ã
  have hAE : A * Em = Em * At Q a := by
    ext x o
    rw [Em_mul]
    rcases o with V | t
    · rw [mul_Em_inl]
      rcases x with ⟨U, b⟩ | s
      · change _ = At Q a (Sum.inl U) (Sum.inl V)
        rw [At_ll, hQ, Matrix.of_apply]
        conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight b)]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Equiv.coe_addRight]
        have := hk U V 0 c b
        rwa [zero_add] at this
      · change _ = At Q a (Sum.inr s) (Sum.inl V)
        rw [At_rl, ha, Matrix.of_apply]
        have e : ∀ c, A (Sum.inr s) (Sum.inl (V, c)) = A (Sum.inl (V, 0)) (Sum.inr s) := by
          intro c
          rw [hsym (Sum.inl (V, c)) (Sum.inr s)]
          have := hk' V 0 s c
          rwa [zero_add] at this
        simp [e]
    · rw [mul_Em_inr]
      rcases x with ⟨U, b⟩ | s
      · change _ = At Q a (Sum.inl U) (Sum.inr t)
        rw [At_lr, ha, Matrix.of_apply]
        have := hk' U 0 t b
        rwa [zero_add] at this
      · change _ = At Q a (Sum.inr s) (Sum.inr t)
        rw [At_rr, htri]
  have hRE : Rm * Em = 1 := by
    ext o o'
    rw [Rm_mul]
    simp [Em, orb_rep, Matrix.one_apply]
  have hRJE : Rm * (J * Em) = Jw := by
    ext o o'
    rw [Rm_mul]
    rcases o' with V | t
    · rw [mul_Em_inl]
      simp [hJ, Jw, wt]
    · rw [mul_Em_inr]
      simp [hJ, Jw, wt]
  have hAt : At Q a = Rm * (A * Em) := by
    rw [hAE, ← Matrix.mul_assoc, hRE, Matrix.one_mul]
  -- Ã² + Ã = 12 I + 2 𝟙 wᵀ
  have hsq : At Q a * At Q a + At Q a =
      (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw := by
    calc At Q a * At Q a + At Q a = Rm * (A * Em) * At Q a + Rm * (A * Em) := by rw [← hAt]
      _ = Rm * (A * (Em * At Q a)) + Rm * (A * Em) := by simp only [Matrix.mul_assoc]
      _ = Rm * (A * (A * Em)) + Rm * (A * Em) := by rw [← hAE]
      _ = Rm * ((A * A + A) * Em) := by rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = Rm * (((12 : ℤ) • (1 : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3)
            ((Fin 32 × ZMod 3) ⊕ Fin 3) ℤ) + (2 : ℤ) • J) * Em) := by rw [hAA]
      _ = (12 : ℤ) • (Rm * Em) + (2 : ℤ) • (Rm * (J * Em)) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul]
      _ = (12 : ℤ) • (1 : Matrix (Fin 32 ⊕ Fin 3) (Fin 32 ⊕ Fin 3) ℤ) + (2 : ℤ) • Jw := by
          rw [hRE, hRJE]
  -- Ã 𝟙 = 14 𝟙
  have hEm1 : Em *ᵥ (fun _ => (1 : ℤ)) = fun _ => 1 := by
    ext x
    simp [Em, mulVec, dotProduct]
  have hrow : At Q a *ᵥ (fun _ => (1 : ℤ)) = fun _ => 14 := by
    rw [hAt, ← mulVec_mulVec, ← mulVec_mulVec, hEm1, hA1]
    ext o
    simp [Rm, mulVec, dotProduct]
  -- reversal of an orbit sum
  have hrev : ∀ U V (b : ZMod 3),
      A (Sum.inl (V, 0)) (Sum.inl (U, b)) = A (Sum.inl (U, 0)) (Sum.inl (V, -b)) := by
    intro U V b
    rw [hsym (Sum.inl (U, b)) (Sum.inl (V, 0))]
    have := hk U V 0 (-b) b
    rwa [zero_add, neg_add_cancel] at this
  have hQs : Qᵀ = Q := by
    ext U V
    simp only [transpose_apply, hQ, Matrix.of_apply]
    simp_rw [hrev U V]
    exact Equiv.sum_comp (Equiv.neg (ZMod 3)) (fun c => A (Sum.inl (U, 0)) (Sum.inl (V, c)))
  have hMh : Mᴴ = M := by
    refine Matrix.ext fun U V => ?_
    simp only [conjTranspose_apply, hM, Matrix.of_apply, star_sum, star_mul', star_intCast,
      star_wpow]
    simp_rw [hrev U V]
    exact Equiv.sum_comp (Equiv.neg (ZMod 3))
      (fun c => ((A (Sum.inl (U, 0)) (Sum.inl (V, c)) : ℤ) : Eis) * wpow c)
  -- the ω-part: A E_ω = E_ω M
  obtain ⟨Aω, hAω⟩ : ∃ Aω : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis,
      Aω = A.map (Int.castRingHom Eis) := ⟨_, rfl⟩
  obtain ⟨Jω, hJω⟩ : ∃ Jω : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3) ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis,
      Jω = Matrix.of fun _ _ => 1 := ⟨_, rfl⟩
  have hAEw : Aω * Ew = Ew * M := by
    refine Matrix.ext fun x V => ?_
    rw [mul_Ew]
    rcases x with ⟨U, b⟩ | s
    · rw [Ew_mul_inl, hM, Matrix.of_apply, Finset.mul_sum]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight b)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Equiv.coe_addRight, hAω, Matrix.map_apply, eq_intCast, wpow_add]
      have := hk U V 0 c b
      rw [zero_add] at this
      rw [this]
      ring
    · rw [Ew_mul_inr]
      have e : ∀ c, Aω (Sum.inr s) (Sum.inl (V, c)) = ((A (Sum.inl (V, 0)) (Sum.inr s) : ℤ) : Eis) := by
        intro c
        simp only [hAω, Matrix.map_apply, eq_intCast]
        rw [hsym (Sum.inl (V, c)) (Sum.inr s)]
        have := hk' V 0 s c
        rw [zero_add] at this
        rw [this]
      simp only [e, ← Finset.mul_sum, sum_wpow, mul_zero]
  have hREw : Rw * Ew = 1 := by
    refine Matrix.ext fun U V => ?_
    rw [Rw_mul]
    simp [Ew, Matrix.one_apply, wpow]
  have hRJEw : Rw * (Jω * Ew) = 0 := by
    refine Matrix.ext fun U V => ?_
    rw [Rw_mul, mul_Ew]
    simp [hJω, sum_wpow]
  have hAAω : Aω * Aω + Aω = (12 : Eis) • (1 : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3)
      ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis) + (2 : Eis) • Jω := by
    have h := congrArg (Int.castRingHom Eis).mapMatrix hAA
    simp only [map_add, map_mul, RingHom.mapMatrix_apply] at h
    rw [← hAω] at h
    rw [h, hJω]
    refine Matrix.ext fun x y => ?_
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hJ,
      Matrix.of_apply, smul_eq_mul]
    by_cases hxy : x = y
    · simp only [hxy, ite_true]
      norm_num
    · simp only [hxy, ite_false]
      norm_num
  have hMrep : M = Rw * (Aω * Ew) := by
    rw [hAEw, ← Matrix.mul_assoc, hREw, Matrix.one_mul]
  have hMM : M * M + M = (12 : Eis) • (1 : Matrix (Fin 32) (Fin 32) Eis) := by
    calc M * M + M = Rw * (Aω * Ew) * M + Rw * (Aω * Ew) := by rw [← hMrep]
      _ = Rw * (Aω * (Ew * M)) + Rw * (Aω * Ew) := by simp only [Matrix.mul_assoc]
      _ = Rw * (Aω * (Aω * Ew)) + Rw * (Aω * Ew) := by rw [← hAEw]
      _ = Rw * ((Aω * Aω + Aω) * Ew) := by rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = Rw * (((12 : Eis) • (1 : Matrix ((Fin 32 × ZMod 3) ⊕ Fin 3)
            ((Fin 32 × ZMod 3) ⊕ Fin 3) Eis) + (2 : Eis) • Jω) * Ew) := by rw [hAAω]
      _ = (12 : Eis) • (Rw * Ew) + (2 : Eis) • (Rw * (Jω * Ew)) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul]
      _ = (12 : Eis) • (1 : Matrix (Fin 32) (Fin 32) Eis) := by
          rw [hREw, hRJEw, smul_zero, add_zero]
  have hQM : M.map Eis.rho = Q.map φ3 := by
    refine Matrix.ext fun U V => ?_
    simp [hM, hQ, map_sum, rho_wpow]
  exact no_triangle_pair Q a M hQs hrow hsq hMh hMM hQM

end Tri

end C3
