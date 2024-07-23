/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity.Basic

/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib.Data.Rat.Cast.Defs`
to avoiding needing to import `Mathlib.Algebra.Field.Basic` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

namespace Rat

variable {α : Type*} [DivisionRing α]

-- Porting note: rewrote proof
@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n
  · simp
  rw [cast_def, inv_natCast_num, inv_natCast_den, if_neg n.succ_ne_zero,
    Int.sign_eq_one_of_pos (Nat.cast_pos.mpr n.succ_pos), Int.cast_one, one_div]

-- Porting note: proof got a lot easier - is this still the intended statement?
@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n n
  · simp [ofInt_eq_cast, cast_inv_nat]
  · simp only [ofInt_eq_cast, Int.cast_negSucc, ← Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]
theorem cast_nnratCast {K} [DivisionRing K] (q : ℚ≥0) :
    ((q : ℚ) : K) = (q : K) := by
  rw [Rat.cast_def, NNRat.cast_def, NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Nat.cast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn, hd, Int.cast_natCast]

/-- Casting a scientific literal via `ℚ` is the same as casting directly. -/
@[simp, norm_cast]
theorem cast_ofScientific {K} [DivisionRing K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K), ← NNRat.cast_ofScientific, cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast]
theorem cast_pow {K} [DivisionSemiring K] (q : ℚ≥0) (n : ℕ) :
    NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Nat.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

theorem cast_zpow_of_ne_zero {K} [DivisionSemiring K] (q : ℚ≥0) (z : ℤ) (hq : (q.num : K) ≠ 0) :
    NNRat.cast (q ^ z) = (NNRat.cast q : K) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

open OfScientific in
theorem Nonneg.coe_ofScientific {K} [LinearOrderedField K] (m : ℕ) (s : Bool) (e : ℕ) :
    (ofScientific m s e : {x : K // 0 ≤ x}).val = ofScientific m s e := rfl

end NNRat

open Function

variable {F ι α β : Type*}

namespace NNRat
section DivisionSemiring
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

lemma cast_injective : Injective ((↑) : ℚ≥0 → α) := by
  rintro p q hpq
  rw [NNRat.cast_def, NNRat.cast_def, Commute.div_eq_div_iff] at hpq
  rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals positivity
  exact Nat.cast_commute _ _

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast] lemma cast_eq_zero : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]
lemma cast_ne_zero : (q : α) ≠ 0 ↔ q ≠ 0 := cast_eq_zero.not

@[simp, norm_cast]
lemma cast_add (p q) : (p + q : ℚ≥0) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

@[simp, norm_cast]
lemma cast_mul (p q) : (p * q : ℚ≥0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

variable (α) in
/-- Coercion `ℚ≥0 → α` as a `RingHom`. -/
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = (↑) := rfl

@[simp, norm_cast]
lemma cast_zpow (q : ℚ≥0) (n : ℤ) : ↑(q ^ n) = ((q : α) ^ n : α) := map_zpow₀ (castHom α) _ _

@[simp, norm_cast] lemma cast_inv (p) : (p⁻¹ : ℚ≥0) = (p : α)⁻¹ := map_inv₀ (castHom α) _
@[simp, norm_cast] lemma cast_div (p q) : (p / q : ℚ≥0) = (p / q : α) := map_div₀ (castHom α) _ _

@[simp, norm_cast]
lemma cast_divNat (a b : ℕ) : (divNat a b : α) = a / b := by
  rw [← cast_natCast, ← cast_natCast b, ← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

end DivisionSemiring
end NNRat
