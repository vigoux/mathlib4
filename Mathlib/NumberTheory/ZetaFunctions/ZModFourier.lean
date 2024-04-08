import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.FourierTransform

open scoped Real

/-- The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`. -/
noncomputable def ZMod.toAddCircle {N : ℕ+} : ZMod N →+ UnitAddCircle :=
  ZMod.lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]), by simp⟩

lemma ZMod.toAddCircle_coe {N : ℕ+} (j : ℤ) :
    ZMod.toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]

lemma ZMod.toAddCircle_apply {N : ℕ+} (j : ZMod N) :
    ZMod.toAddCircle j = ↑(j.val / N : ℝ) := by
  conv_lhs => rw [show j = (val j : ℤ) by simp, ZMod.toAddCircle_coe]

lemma ZMod.toAddCircle_injective (N : ℕ+) : Function.Injective <| toAddCircle (N := N) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr N.pos
  rw [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hp := Real.fact_zero_lt_one) (a := 0), div_left_inj' this.ne', Nat.cast_inj] at hxy
  · exact ZMod.val_injective N hxy
  all_goals
  · refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one this, Nat.cast_lt]
    exact ZMod.val_lt _

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
noncomputable def ZMod.toCircle {N : ℕ+} : AddChar (ZMod N) circle where
  toFun := fun j ↦ (ZMod.toAddCircle j).toCircle
  map_add_mul' a b := by simp_rw [map_add, AddCircle.toCircle_add]
  map_zero_one' := by simp_rw [map_zero, AddCircle.toCircle, ← QuotientAddGroup.mk_zero,
    Function.Periodic.lift_coe, mul_zero, expMapCircle_zero]

lemma ZMod.toCircle_coe {N : ℕ+} (j : ℤ) :
    ZMod.toCircle (j : ZMod N) = Complex.exp (2 * π * Complex.I * j / N) := by
  rw [ZMod.toCircle, AddChar.coe_mk, AddCircle.toCircle, ZMod.toAddCircle_coe,
    Function.Periodic.lift_coe, expMapCircle_apply]
  push_cast
  ring_nf

lemma ZMod.toCircle_apply {N : ℕ+} (j : ZMod N) :
    ZMod.toCircle j = Complex.exp (2 * π * Complex.I * j.val / N) := by
  rw [← Int.cast_natCast, ← ZMod.toCircle_coe, ZMod.nat_cast_val, ZMod.int_cast_zmod_cast]


section fourier

open BigOperators MeasureTheory

namespace ZMod

/-- Auxiliary lemma to translate integrability statements into summability -/
lemma integrable_count_iff {𝓚 G : Type*} [NormedAddCommGroup G]
    [SecondCountableTopology G] {f : 𝓚 → G} :
    Integrable f (@Measure.count _ ⊤) ↔ Summable (fun k ↦ ‖f k‖) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace 𝓚 := ⊤
  simp_rw [Integrable, eq_true_intro (by measurability : AEStronglyMeasurable f Measure.count),
    true_and, HasFiniteIntegral, lintegral_count, lt_top_iff_ne_top,
    ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe, coe_nnnorm]

lemma Finite.summable {α M : Type*} [Finite α] [AddCommMonoid M] [TopologicalSpace M]
    (f : α → M) : Summable f :=
  summable_of_finite_support <| Set.finite_univ.subset (Set.subset_univ _)

/-- The discrete measurable space structure (every set is measurable). -/
local instance instMeasurableSpaceZMod (N : ℕ+) : MeasurableSpace (ZMod N) := ⊤

/-- The discrete Fourier transform on `ℤ / Nℤ`. -/
noncomputable def discreteFourierTransform {N : ℕ+} (Φ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  Fourier.fourierIntegral ZMod.toCircle Measure.count Φ k

@[inherit_doc]
scoped notation "𝓕" => discreteFourierTransform

lemma discreteFourierTransform_def {N : ℕ+} (Φ : ZMod N → ℂ) (k : ZMod N) :
    discreteFourierTransform Φ k = ∑ j : ZMod N, ZMod.toCircle (-(j * k)) • Φ j := by
  rw [discreteFourierTransform, Fourier.fourierIntegral_def,
    integral_countable' (integrable_count_iff.mpr <| Finite.summable _), tsum_fintype]
  congr 1 with j
  simp_rw [Measure.count_singleton, ENNReal.one_toReal, one_smul]

end ZMod

end fourier
