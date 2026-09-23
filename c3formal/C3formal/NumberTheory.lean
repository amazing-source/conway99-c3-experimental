import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# The arithmetic of the two determinants

* `int_mod3_eq_two` : if `0 < d`, `d ∣ 77^r`, `33 d = t² g` and `11 ∤ g`, then `d ≡ 2 (mod 3)`:
  the 11-adic valuation of `d` is odd, and `d = 7^a 11^b`.
* `int_mod3_eq_one` : a positive divisor of `7^r` is `≡ 1 (mod 3)`.
-/

namespace C3

theorem two_pow_odd (e : ℕ) (he : Odd e) : (2 : ZMod 3) ^ e = 2 := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_succ, pow_mul]
  have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [h4, one_pow, one_mul]

theorem nat_mod3_eq_two (D T G r : ℕ) (hD : 0 < D) (hdvd : D ∣ 77 ^ r) (hG : ¬ 11 ∣ G)
    (h : 33 * D = T ^ 2 * G) : (D : ZMod 3) = 2 := by
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
  have h33 : padicValNat 11 33 = 1 := by
    rw [show (33 : ℕ) = 11 * 3 by norm_num,
      padicValNat.mul (by norm_num : (11 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0),
      padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have v1 : padicValNat 11 (33 * (11 ^ e * D0)) = 1 + e := by
    rw [padicValNat.mul (by norm_num : (33 : ℕ) ≠ 0) (by positivity : 11 ^ e * D0 ≠ 0), h33,
      padicValNat.mul (by positivity : (11 : ℕ) ^ e ≠ 0) hD0pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hD0, add_zero]
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

theorem int_mod3_eq_two (d t g : ℤ) (r : ℕ) (hd : 0 < d) (hdvd : d ∣ 77 ^ r)
    (hg : ¬ (11 : ℤ) ∣ g) (h : 33 * d = t ^ 2 * g) : (d : ZMod 3) = 2 := by
  have hD : 0 < d.natAbs := Int.natAbs_pos.mpr hd.ne'
  have hdvd' : d.natAbs ∣ 77 ^ r := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have hg' : ¬ 11 ∣ g.natAbs := fun h11 => hg (Int.ofNat_dvd_left.mpr h11)
  have h' : 33 * d.natAbs = t.natAbs ^ 2 * g.natAbs := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have key := nat_mod3_eq_two _ _ _ r hD hdvd' hg' h'
  have hdeq : ((d.natAbs : ℕ) : ℤ) = d := Int.natAbs_of_nonneg hd.le
  rw [← hdeq, Int.cast_natCast]
  exact key

theorem int_mod3_eq_one (d k : ℤ) (r : ℕ) (hd : 0 < d) (h : d * k = 7 ^ r) :
    (d : ZMod 3) = 1 := by
  have hdvd : d.natAbs ∣ 7 ^ r := by
    have h1 : d ∣ 7 ^ r := Dvd.intro k h
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdvd
  have hdeq : d = ((7 ^ a : ℕ) : ℤ) := by rw [← ha, Int.natAbs_of_nonneg hd.le]
  rw [hdeq]
  push_cast
  have h7 : (7 : ZMod 3) = 1 := by decide
  rw [h7, one_pow]

end C3
