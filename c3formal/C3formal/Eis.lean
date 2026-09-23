import Mathlib.Algebra.Star.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Eisenstein integers `ℤ[ω]`

`Eis` is the ring `ℤ[ω]` with `ω² + ω + 1 = 0`; the structure `⟨a, b⟩` stands for `a + b ω`.

We provide
* the commutative ring structure;
* complex conjugation (`ω ↦ ω² = -1 - ω`) as a `StarRing` structure;
* the reduction `rho : Eis →+* ZMod 3`, `ω ↦ 1` (its kernel is the prime `(1 - ω)`),
  which is compatible with conjugation.
-/

@[ext]
structure Eis where
  re : ℤ
  im : ℤ
deriving DecidableEq

namespace Eis

/-- The integer `n` as an Eisenstein integer. -/
def ofInt (n : ℤ) : Eis := ⟨n, 0⟩

@[simp] theorem re_ofInt (n : ℤ) : (ofInt n).re = n := rfl
@[simp] theorem im_ofInt (n : ℤ) : (ofInt n).im = 0 := rfl

instance : Zero Eis := ⟨ofInt 0⟩
@[simp] theorem re_zero : (0 : Eis).re = 0 := rfl
@[simp] theorem im_zero : (0 : Eis).im = 0 := rfl

instance : One Eis := ⟨ofInt 1⟩
@[simp] theorem re_one : (1 : Eis).re = 1 := rfl
@[simp] theorem im_one : (1 : Eis).im = 0 := rfl

/-- The primitive cube root of unity `ω`. -/
def w : Eis := ⟨0, 1⟩
@[simp] theorem re_w : w.re = 0 := rfl
@[simp] theorem im_w : w.im = 1 := rfl

instance : Add Eis := ⟨fun z v => ⟨z.re + v.re, z.im + v.im⟩⟩
@[simp] theorem re_add (z v : Eis) : (z + v).re = z.re + v.re := rfl
@[simp] theorem im_add (z v : Eis) : (z + v).im = z.im + v.im := rfl

instance : Neg Eis := ⟨fun z => ⟨-z.re, -z.im⟩⟩
@[simp] theorem re_neg (z : Eis) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : Eis) : (-z).im = -z.im := rfl

/-- `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) ω`, using `ω² = -1 - ω`. -/
instance : Mul Eis :=
  ⟨fun z v => ⟨z.re * v.re - z.im * v.im, z.re * v.im + z.im * v.re - z.im * v.im⟩⟩
@[simp] theorem re_mul (z v : Eis) : (z * v).re = z.re * v.re - z.im * v.im := rfl
@[simp] theorem im_mul (z v : Eis) :
    (z * v).im = z.re * v.im + z.im * v.re - z.im * v.im := rfl

instance addCommGroup : AddCommGroup Eis := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec Eis ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec Eis ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Eis ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp] theorem re_sub (z v : Eis) : (z - v).re = z.re - v.re := rfl
@[simp] theorem im_sub (z v : Eis) : (z - v).im = z.im - v.im := rfl

instance addGroupWithOne : AddGroupWithOne Eis :=
  { Eis.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

instance commRing : CommRing Eis := by
  refine
  { Eis.addGroupWithOne with
    npow := @npowRec Eis ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

@[simp] theorem re_intCast (n : ℤ) : (n : Eis).re = n := rfl
@[simp] theorem im_intCast (n : ℤ) : (n : Eis).im = 0 := rfl
@[simp] theorem re_natCast (n : ℕ) : (n : Eis).re = n := rfl
@[simp] theorem im_natCast (n : ℕ) : (n : Eis).im = 0 := rfl

@[simp] theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Eis).re = OfNat.ofNat n := rfl
@[simp] theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Eis).im = 0 := rfl

theorem w_sq : w * w = -1 - w := by ext <;> simp

/-! ### Complex conjugation -/

/-- Complex conjugation: `ω ↦ ω² = -1 - ω`, i.e. `a + bω ↦ (a - b) - bω`. -/
instance : Star Eis := ⟨fun z => ⟨z.re - z.im, -z.im⟩⟩
@[simp] theorem re_star (z : Eis) : (star z).re = z.re - z.im := rfl
@[simp] theorem im_star (z : Eis) : (star z).im = -z.im := rfl

instance : StarRing Eis where
  star_involutive z := by ext <;> simp
  star_mul z v := by ext <;> simp <;> ring
  star_add z v := by ext <;> simp <;> ring

/-- An Eisenstein integer fixed by conjugation is a rational integer. -/
theorem eq_intCast_of_star_eq {z : Eis} (h : star z = z) : z = (z.re : Eis) := by
  have him : z.im = 0 := by
    have := congrArg Eis.im h
    simp at this
    omega
  ext <;> simp [him]

theorem intCast_injective : Function.Injective (Int.cast : ℤ → Eis) := by
  intro a b h
  simpa using congrArg Eis.re h

/-! ### Reduction modulo `1 - ω` -/

/-- The reduction `ℤ[ω] → ℤ[ω]/(1 - ω) ≅ 𝔽₃`, `ω ↦ 1`. -/
def rho : Eis →+* ZMod 3 where
  toFun z := ((z.re + z.im : ℤ) : ZMod 3)
  map_one' := by simp
  map_mul' z v := by
    rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨z.im * v.im, by simp only [re_mul, im_mul]; push_cast; ring⟩
  map_zero' := by simp
  map_add' z v := by
    rw [← Int.cast_add]
    congr 1
    simp only [re_add, im_add]
    ring

theorem rho_apply (z : Eis) : rho z = ((z.re + z.im : ℤ) : ZMod 3) := rfl

@[simp] theorem rho_star (z : Eis) : rho (star z) = rho z := by
  rw [rho_apply, rho_apply, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact ⟨z.im, by simp only [re_star, im_star]; push_cast; ring⟩

@[simp] theorem rho_w : rho w = 1 := by
  rw [rho_apply]
  simp

@[simp] theorem rho_intCast (n : ℤ) : rho (n : Eis) = (n : ZMod 3) := by
  rw [rho_apply]
  simp

end Eis
