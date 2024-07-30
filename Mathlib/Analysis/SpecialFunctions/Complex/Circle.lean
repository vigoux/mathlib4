/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `expMapCircle` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `circle` and `ℝ`, see
`circle.argPartialEquiv` and `circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/


open Complex Function Set

open Real

namespace circle

theorem injective_arg : Injective fun z : circle => arg z := fun z w h =>
  Subtype.ext <| ext_abs_arg ((abs_coe_circle z).trans (abs_coe_circle w).symm) h

@[simp]
theorem arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff

end circle

theorem arg_expMapCircle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (expMapCircle x) = x := by
  rw [expMapCircle_apply, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp]
theorem expMapCircle_arg (z : circle) : expMapCircle (arg z) = z :=
  circle.injective_arg <| arg_expMapCircle (neg_pi_lt_arg _) (arg_le_pi _)

namespace circle

/-- `Complex.arg ∘ (↑)` and `expMapCircle` define a partial equivalence between `circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps (config := .asFn)]
noncomputable def argPartialEquiv : PartialEquiv circle ℝ where
  toFun := arg ∘ (↑)
  invFun := expMapCircle
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := expMapCircle_arg z
  right_inv' _ hx := arg_expMapCircle hx.1 hx.2

/-- `Complex.arg` and `expMapCircle` define an equivalence between `circle` and `(-π, π]`. -/
@[simps (config := .asFn)]
noncomputable def argEquiv : circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := expMapCircle ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
  right_inv x := Subtype.ext <| argPartialEquiv.right_inv x.2

end circle

theorem leftInverse_expMapCircle_arg : LeftInverse expMapCircle (arg ∘ (↑)) :=
  expMapCircle_arg

theorem invOn_arg_expMapCircle : InvOn (arg ∘ (↑)) expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.invOn

theorem surjOn_expMapCircle_neg_pi_pi : SurjOn expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.surjOn

theorem expMapCircle_eq_expMapCircle {x y : ℝ} :
    expMapCircle x = expMapCircle y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, expMapCircle_apply, expMapCircle_apply, exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast

theorem periodic_expMapCircle : Periodic expMapCircle (2 * π) := fun z =>
  expMapCircle_eq_expMapCircle.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

@[simp]
theorem expMapCircle_two_pi : expMapCircle (2 * π) = 1 :=
  periodic_expMapCircle.eq.trans expMapCircle_zero

theorem expMapCircle_sub_two_pi (x : ℝ) : expMapCircle (x - 2 * π) = expMapCircle x :=
  periodic_expMapCircle.sub_eq x

theorem expMapCircle_add_two_pi (x : ℝ) : expMapCircle (x + 2 * π) = expMapCircle x :=
  periodic_expMapCircle x

/-- `expMapCircle`, applied to a `Real.Angle`. -/
noncomputable def Real.Angle.expMapCircle (θ : Real.Angle) : circle :=
  periodic_expMapCircle.lift θ

@[simp]
theorem Real.Angle.expMapCircle_coe (x : ℝ) : Real.Angle.expMapCircle x = _root_.expMapCircle x :=
  rfl

theorem Real.Angle.coe_expMapCircle (θ : Real.Angle) :
    (θ.expMapCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Real.Angle.induction_on
  simp [exp_mul_I]

@[simp]
theorem Real.Angle.expMapCircle_zero : Real.Angle.expMapCircle 0 = 1 := by
  rw [← Real.Angle.coe_zero, Real.Angle.expMapCircle_coe, _root_.expMapCircle_zero]

@[simp]
theorem Real.Angle.expMapCircle_neg (θ : Real.Angle) :
    Real.Angle.expMapCircle (-θ) = (Real.Angle.expMapCircle θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  simp_rw [← Real.Angle.coe_neg, Real.Angle.expMapCircle_coe, _root_.expMapCircle_neg]

@[simp]
theorem Real.Angle.expMapCircle_add (θ₁ θ₂ : Real.Angle) : Real.Angle.expMapCircle (θ₁ + θ₂) =
    Real.Angle.expMapCircle θ₁ * Real.Angle.expMapCircle θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact _root_.expMapCircle_add _ _

@[simp]
theorem Real.Angle.arg_expMapCircle (θ : Real.Angle) :
    (arg (Real.Angle.expMapCircle θ) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.expMapCircle_coe, expMapCircle_apply, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Real.Angle.cos_coe, ← Real.Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]

namespace AddCircle

variable {T : ℝ}

/-! ### Map from `AddCircle` to `Circle` -/

theorem scaled_exp_map_periodic : Function.Periodic (fun x => expMapCircle (2 * π / T * x)) T := by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · intro x; simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, periodic_expMapCircle]

/-- The canonical map `fun x => exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
noncomputable def toCircle : AddCircle T → circle :=
  (@scaled_exp_map_periodic T).lift

theorem toCircle_apply_mk (x : ℝ) : @toCircle T x = expMapCircle (2 * π / T * x) :=
  rfl

theorem toCircle_add (x : AddCircle T) (y : AddCircle T) :
    @toCircle T (x + y) = toCircle x * toCircle y := by
  induction x using QuotientAddGroup.induction_on'
  induction y using QuotientAddGroup.induction_on'
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, expMapCircle_add]

lemma toCircle_zero : toCircle (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero, toCircle_apply_mk, mul_zero, expMapCircle_zero]

theorem continuous_toCircle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (expMapCircle.continuous.comp <| continuous_const.mul continuous_id')

theorem injective_toCircle (hT : T ≠ 0) : Function.Injective (@toCircle T) := by
  intro a b h
  induction a using QuotientAddGroup.induction_on'
  induction b using QuotientAddGroup.induction_on'
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := expMapCircle_eq_expMapCircle.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  rw [← mul_right_inj' Real.two_pi_pos.ne']
  linarith

/-- The homeomorphism between `AddCircle (2 * π)` and `circle`. -/
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ circle where
  toFun := Angle.expMapCircle
  invFun := fun x ↦ arg x
  left_inv := Angle.arg_expMapCircle
  right_inv := expMapCircle_arg
  continuous_toFun := continuous_coinduced_dom.mpr expMapCircle.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    apply (continuousAt_arg_coe_angle (ne_zero_of_mem_circle x)).comp
      continuousAt_subtype_val

theorem homeomorphCircle'_apply_mk (x : ℝ) : homeomorphCircle' x = expMapCircle x :=
  rfl

/-- The homeomorphism between `AddCircle` and `circle`. -/
noncomputable def homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ circle :=
  (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'

theorem homeomorphCircle_apply (hT : T ≠ 0) (x : AddCircle T) :
    homeomorphCircle hT x = toCircle x := by
  induction' x using QuotientAddGroup.induction_on' with x
  rw [homeomorphCircle, Homeomorph.trans_apply,
    homeomorphAddCircle_apply_mk, homeomorphCircle'_apply_mk, toCircle_apply_mk]
  ring_nf

/-- The canoncial map from the additive to the multiplicative circle, as an `AddChar`. -/
noncomputable def toCircle_addChar : AddChar (AddCircle T) circle where
  toFun := toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

end AddCircle

open AddCircle

-- todo: upgrade this to `IsCoveringMap expMapCircle`.
lemma isLocalHomeomorph_expMapCircle : IsLocalHomeomorph expMapCircle := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  exact homeomorphCircle'.isLocalHomeomorph.comp (isLocalHomeomorph_coe (2 * π))

namespace ZMod

/-!
### Additive characters valued in the complex circle
-/

open scoped Real

variable {N : ℕ} [NeZero N]

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
noncomputable def toCircle : AddChar (ZMod N) circle :=
  toCircle_addChar.compAddMonoidHom toAddCircle

lemma toCircle_intCast (j : ℤ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [toCircle, AddChar.compAddMonoidHom_apply, toCircle_addChar, AddChar.coe_mk,
    AddCircle.toCircle, toAddCircle_intCast, Function.Periodic.lift_coe, expMapCircle_apply]
  push_cast
  ring_nf

lemma toCircle_natCast (j : ℕ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  simpa using toCircle_intCast (N := N) j

/--
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMod.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toCircle_intCast` instead.
-/
lemma toCircle_apply (j : ZMod N) :
    toCircle j = exp (2 * π * I * j.val / N) := by
  rw [← toCircle_natCast, natCast_zmod_val]

lemma injective_toCircle : Injective (toCircle : ZMod N → circle) :=
  (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

/-- The additive character from `ZMod N` to `ℂ`, sending `j mod N` to `exp (2 * π * I * j / N)`. -/
noncomputable def stdAddChar : AddChar (ZMod N) ℂ := circle.subtype.compAddChar toCircle

lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by
  simp only [stdAddChar, MonoidHom.coe_compAddChar, Function.comp_apply,
    Submonoid.coe_subtype, toCircle_intCast]

lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl

lemma injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) ℂ) :=
  Subtype.coe_injective.comp injective_toCircle

/-- The standard additive character `ZMod N → ℂ` is primitive. -/
lemma isPrimitive_stdAddChar (N : ℕ) [NeZero N] :
     (stdAddChar (N := N)).IsPrimitive := by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht ↦ ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

end ZMod
