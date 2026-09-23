import C3formal.Eis
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# `ℤ[ω]` is a Euclidean domain

Norm `N(a + bω) = a² - ab + b² = z * star z`; division by rounding each coordinate of
`x * star y / N(y)`, which leaves a remainder of norm `≤ 3/4 N(y) < N(y)`.
Consequences used later: `IsDomain Eis`, `IsPrincipalIdealRing Eis`.
-/

namespace Eis

/-- The norm `N(a + bω) = a² - ab + b²`. -/
def norm (z : Eis) : ℤ := z.re * z.re - z.re * z.im + z.im * z.im

theorem norm_mul (z v : Eis) : norm (z * v) = norm z * norm v := by
  simp only [norm, re_mul, im_mul]
  ring

theorem norm_star (z : Eis) : norm (star z) = norm z := by
  simp only [norm, re_star, im_star]
  ring

theorem norm_nonneg (z : Eis) : 0 ≤ norm z := by
  unfold norm
  nlinarith [mul_self_nonneg (z.re - z.im), mul_self_nonneg z.re, mul_self_nonneg z.im]

theorem norm_eq_zero {z : Eis} : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold norm at h
    have hsum : z.re * z.re + z.im * z.im + (z.re - z.im) * (z.re - z.im) = 0 := by
      linear_combination 2 * h
    have h1 : z.re * z.re = 0 := by
      nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im, mul_self_nonneg (z.re - z.im)]
    have h2 : z.im * z.im = 0 := by
      nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im, mul_self_nonneg (z.re - z.im)]
    ext
    · simpa using mul_self_eq_zero.mp h1
    · simpa using mul_self_eq_zero.mp h2
  · rintro rfl
    simp [norm]

theorem norm_pos {z : Eis} (hz : z ≠ 0) : 0 < norm z :=
  lt_of_le_of_ne (norm_nonneg z) (fun h => hz (norm_eq_zero.mp h.symm))

theorem mul_star_self (z : Eis) : z * star z = (norm z : Eis) := by
  ext <;> simp [norm] <;> ring

instance : Nontrivial Eis := ⟨⟨0, 1, by simp [Eis.ext_iff]⟩⟩

instance : NoZeroDivisors Eis where
  eq_zero_or_eq_zero_of_mul_eq_zero {z v} h := by
    have := congrArg norm h
    rw [norm_mul] at this
    have h0 : norm 0 = 0 := by simp [norm]
    rw [h0] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (norm_eq_zero.mp h1)
    · exact Or.inr (norm_eq_zero.mp h1)

instance : IsDomain Eis := NoZeroDivisors.to_isDomain Eis

/-! ### Division with remainder -/

/-- Rounded division: `rdiv a n ≈ a / n`, with `|a - n * rdiv a n| ≤ n / 2` for `n > 0`. -/
def rdiv (a n : ℤ) : ℤ := (2 * a + n) / (2 * n)

theorem rdiv_spec (a n : ℤ) (hn : 0 < n) :
    -n ≤ 2 * (a - n * rdiv a n) ∧ 2 * (a - n * rdiv a n) ≤ n := by
  unfold rdiv
  have h2n : 0 < 2 * n := by omega
  have hq := Int.mul_ediv_add_emod (2 * a + n) (2 * n)
  have hr0 := Int.emod_nonneg (2 * a + n) (ne_of_gt h2n)
  have hr1 := Int.emod_lt_of_pos (2 * a + n) h2n
  constructor <;> linarith

instance : Div Eis :=
  ⟨fun x y => ⟨rdiv (x * star y).re (norm y), rdiv (x * star y).im (norm y)⟩⟩

theorem div_def (x y : Eis) :
    x / y = ⟨rdiv (x * star y).re (norm y), rdiv (x * star y).im (norm y)⟩ := rfl

instance : Mod Eis := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : Eis) : x % y = x - y * (x / y) := rfl

theorem norm_mod_lt (x : Eis) {y : Eis} (hy : y ≠ 0) : norm (x % y) < norm y := by
  have hn : 0 < norm y := norm_pos hy
  set n := norm y with hndef
  set q := x / y with hqdef
  set c := x * star y with hcdef
  set e1 := c.re - n * q.re with he1
  set e2 := c.im - n * q.im with he2
  -- (x % y) * star y = c - q * n
  have key : (x % y) * star y = ⟨e1, e2⟩ := by
    have h1 : (x % y) * star y = c - q * (y * star y) := by
      rw [mod_def, hcdef]; ring
    rw [h1, mul_star_self]
    ext <;> simp [he1, he2] <;> ring
  have hnorm : norm (x % y) * n = e1 * e1 - e1 * e2 + e2 * e2 := by
    have := congrArg norm key
    rw [norm_mul, norm_star] at this
    rw [this]
    simp [norm]
  have hq1 : q.re = rdiv c.re n := by rw [hqdef, div_def]
  have hq2 : q.im = rdiv c.im n := by rw [hqdef, div_def]
  obtain ⟨a1, a2⟩ := rdiv_spec c.re n hn
  obtain ⟨b1, b2⟩ := rdiv_spec c.im n hn
  rw [← hq1] at a1 a2
  rw [← hq2] at b1 b2
  have hA1 : -n ≤ 2 * e1 := by rw [he1]; exact a1
  have hA2 : 2 * e1 ≤ n := by rw [he1]; exact a2
  have hB1 : -n ≤ 2 * e2 := by rw [he2]; exact b1
  have hB2 : 2 * e2 ≤ n := by rw [he2]; exact b2
  have hbound : 4 * (e1 * e1 - e1 * e2 + e2 * e2) ≤ 3 * (n * n) := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * e1) (by linarith : (0:ℤ) ≤ n + 2 * e1),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * e2) (by linarith : (0:ℤ) ≤ n + 2 * e2),
      mul_nonneg (by linarith : (0:ℤ) ≤ n + 2 * e1) (by linarith : (0:ℤ) ≤ n + 2 * e2),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * e1) (by linarith : (0:ℤ) ≤ n - 2 * e2)]
  have h0 := norm_nonneg (x % y)
  nlinarith

theorem natAbs_norm_mod_lt (x : Eis) {y : Eis} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  have h1 := norm_mod_lt x hy
  have h2 := norm_nonneg (x % y)
  omega

theorem norm_le_norm_mul_left (x : Eis) {y : Eis} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul]
  have h1 := norm_pos hy
  have h2 := norm_nonneg x
  have h3 : norm x ≤ norm x * norm y := by nlinarith
  omega

instance : EuclideanDomain Eis :=
  { Eis.commRing, (inferInstance : Nontrivial Eis) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by
      rw [div_def]
      ext <;> simp [rdiv, norm]
    quotient_mul_add_remainder_eq := fun _ _ => by rw [mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

instance : IsPrincipalIdealRing Eis := inferInstance

end Eis
