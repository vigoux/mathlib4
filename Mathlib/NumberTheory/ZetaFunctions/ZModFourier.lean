/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.LegendreSymbol.GaussSum

/-!
# Fourier theory on `ZMod N`

This file just records a few minimalistic definitions about discrete Fourier transforms for
functions on `ZMod N`.
-/


open scoped Real

namespace ZMod

/-- The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`. -/
noncomputable def toAddCircle {N : ℕ+} : ZMod N →+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]), by simp⟩

lemma toAddCircle_coe {N : ℕ+} (j : ℤ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]

lemma toAddCircle_apply {N : ℕ+} (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : ℝ) := by
  conv_lhs => rw [show j = (val j : ℤ) by simp, toAddCircle_coe]
  rfl

lemma toAddCircle_injective (N : ℕ+) : Function.Injective <| toAddCircle (N := N) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr N.pos
  rw [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hp := Real.fact_zero_lt_one) (a := 0), div_left_inj' this.ne', Nat.cast_inj] at hxy
  · exact val_injective N hxy
  all_goals
  · refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one this, Nat.cast_lt]
    exact val_lt _

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
noncomputable def toCircle {N : ℕ+} : AddChar (ZMod N) circle where
  toFun := fun j ↦ (toAddCircle j).toCircle
  map_add_mul' a b := by simp_rw [map_add, AddCircle.toCircle_add]
  map_zero_one' := by simp_rw [map_zero, AddCircle.toCircle, ← QuotientAddGroup.mk_zero,
    Function.Periodic.lift_coe, mul_zero, expMapCircle_zero]

lemma toCircle_coe {N : ℕ+} (j : ℤ) :
    toCircle (j : ZMod N) = Complex.exp (2 * π * Complex.I * j / N) := by
  rw [toCircle, AddChar.coe_mk, AddCircle.toCircle, toAddCircle_coe,
    Function.Periodic.lift_coe, expMapCircle_apply]
  push_cast
  ring_nf

lemma toCircle_apply {N : ℕ+} (j : ZMod N) :
    toCircle j = Complex.exp (2 * π * Complex.I * j.val / N) := by
  rw [← Int.cast_natCast, ← toCircle_coe, natCast_val, intCast_zmod_cast]

/-- The additive character from `ZMod N` to the underlying multiplicative monoid of `ℂ`, sending
`j mod N` to `exp (2 * π * I * j / N)`. -/
noncomputable def stdAddChar {N : ℕ+} : AddChar (ZMod N) ℂ :=
  (Submonoid.subtype circle).compAddChar toCircle

lemma stdAddChar_coe {N : ℕ+} (j : ℤ) :
    stdAddChar (j : ZMod N) = Complex.exp (2 * π * Complex.I * j / N) := by
  simp only [stdAddChar, MonoidHom.coe_compAddChar, Function.comp_apply,
    Submonoid.coe_subtype, toCircle_coe]

lemma stdAddChar_apply {N : ℕ+} (j : ZMod N) :
    stdAddChar j = ↑(toCircle j) :=
  rfl

section fourier

open BigOperators MeasureTheory


/-- Auxiliary lemma to translate integrability statements into summability -/
lemma integrable_count_iff {𝓚 G : Type*} [NormedAddCommGroup G]
    [SecondCountableTopology G] {f : 𝓚 → G} :
    Integrable f (@Measure.count _ ⊤) ↔ Summable (fun k ↦ ‖f k‖) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace 𝓚 := ⊤
  simp_rw [Integrable, (by measurability : AEStronglyMeasurable f Measure.count),
    true_and, HasFiniteIntegral, lintegral_count, lt_top_iff_ne_top,
    ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe, coe_nnnorm]

lemma Finite.summable {α M : Type*} [Finite α] [AddCommMonoid M] [TopologicalSpace M]
    (f : α → M) : Summable f :=
  summable_of_finite_support <| Set.finite_univ.subset (Set.subset_univ _)

/-- The discrete measurable space structure (every set is measurable). -/
local instance instMeasurableSpaceZMod (N : ℕ+) : MeasurableSpace (ZMod N) := ⊤

/-- The discrete Fourier transform on `ℤ / Nℤ`. -/
noncomputable def discreteFourierTransform {N : ℕ+} (Φ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  Fourier.fourierIntegral toCircle Measure.count Φ k

@[inherit_doc]
scoped notation "𝓕" => discreteFourierTransform

lemma discreteFourierTransform_def {N : ℕ+} (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, toCircle (-(j * k)) • Φ j := by
  simp only [discreteFourierTransform, Fourier.fourierIntegral_def,
    integral_countable' (integrable_count_iff.mpr <| Finite.summable _), Measure.count_singleton,
    ENNReal.one_toReal, one_smul, tsum_fintype]

section GaussSum

variable {N : ℕ+} (χ : MulChar (ZMod N) ℂ)

lemma fourierTransform_eq_gaussSum_mulShift (k : ZMod N) :
    (𝓕 χ) k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp_rw [gaussSum, discreteFourierTransform_def, Submonoid.smul_def, smul_eq_mul,
    mul_comm (χ _)]
  refine congr_arg Finset.univ.sum (funext fun j ↦ ?_)
  simp_rw [AddChar.mulShift_apply, stdAddChar_apply, mul_comm j, neg_mul]

end GaussSum


end fourier

end ZMod
