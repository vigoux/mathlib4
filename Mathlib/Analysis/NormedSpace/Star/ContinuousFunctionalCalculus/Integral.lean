/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Spectrum

/-!
# The continuous functional calculus and integrals

FIXME

## Main declarations

FIXME

## Implementation notes

FIXME
-/

open scoped MeasureTheory

section CLM

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]

--MOVEME
noncomputable def cfcCLM {a : A} (ha : p a) : C(spectrum R a, R) →L[R] A :=
  { cfcHom ha with
    map_smul' := fun c f => by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
        OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
        LinearMapClass.map_smul, StarAlgHom.coe_toAlgHom, RingHom.id_apply]
    cont := (cfcHom_closedEmbedding ha).continuous }

lemma cfc_eq_cfcCLM {a : A} {f : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    cfc f a = cfcCLM ha ⟨_, hf.restrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩]
  rfl

lemma cfcHom_eq_cfcCLM {a : A} {f : C(spectrum R a, R)} (ha : p a) :
    cfcHom ha f = cfcCLM ha f := rfl

end CLM

section integral

variable {X : Type*} {A : Type*} {p : A → Prop} [MeasurableSpace X]
  [NormedRing A] [StarRing A]
  [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ p] {μ : MeasureTheory.Measure X}

variable {b : A}

open MeasureTheory in
lemma cfcCLM_integral (a : A) (ha : p a) (f : X → C(spectrum ℝ a, ℝ))
    (hf₁ : Integrable f μ) :
    ∫ x, cfcCLM ha (f x) ∂μ = cfcCLM ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

open MeasureTheory in
lemma cfcHom_integral (a : A) (ha : p a) (f : X → C(spectrum ℝ a, ℝ))
    (hf₁ : Integrable f μ) :
    ∫ x, cfcHom ha (f x) ∂μ = cfcHom ha (∫ x, f x ∂μ) := by
  have h₁ : ∫ x, cfcHom ha (f x) ∂μ = ∫ x, cfcCLM ha (f x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [cfcHom_eq_cfcCLM ha]
  rw [h₁, cfcHom_eq_cfcCLM ha]
  exact cfcCLM_integral a ha (fun x ↦ f x) hf₁

-- might need to prove a ProperSpace instance on C(α, R) for compact α, which gives us that the
-- space has a second countable topology. This then implies that continuous implies
-- AEStronglyMeasurable (`ContinuousOn.aestronglyMeasurable`)
-- Or not: I can just assume SecondCountableTopology on `X`.

-- FIXME: generalize to RCLike 𝕜
open MeasureTheory in
lemma cfc_integral [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (f : X → ℝ → ℝ) (a : A) (ha : p a)
    (hf₁ : Integrable (fun x => sSup ((norm ∘ f x) '' spectrum ℝ a)) μ)
    (hf₂ : ∀ x, ContinuousOn (f x) (spectrum ℝ a))  -- make this ∀ᵐ x ∂μ
    (hf₃ : ContinuousOn (fun r => ∫ x, f x r ∂μ) (spectrum ℝ a)) :
    ∫ x, cfc (f x) a ∂μ = cfc (fun r => ∫ x, f x r ∂μ) a := by
  let fc : X → C(spectrum ℝ a, ℝ) := fun x => ⟨_, (hf₂ x).restrict⟩
  have h₁ : ∫ x, cfc (f x) a ∂μ = ∫ x, cfcCLM ha (fc x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [cfc_eq_cfcCLM ha (hf₂ x)]
  have fc_continuous : Continuous fc := by sorry
  have hmain : Integrable fc μ := by
    refine ⟨Continuous.aestronglyMeasurable fc_continuous, ?_⟩
    sorry
  rw [h₁, cfc_eq_cfcCLM ha hf₃]
  rw [ContinuousLinearMap.integral_comp_comm _ hmain]
  congr 1
  ext r
  conv_lhs => change ContinuousMap.evalCLM ℝ r (∫ x, fc x ∂μ)
  rw [← ContinuousLinearMap.integral_comp_comm _ hmain]
  rfl

end integral
