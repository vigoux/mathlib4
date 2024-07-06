/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`.

### Main definitions and results

* `ZMod.dft`: the Fourier transform with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

open scoped Real

open MeasureTheory Finset

/-- A function is _even_ if it satisfis `f (-x) = f x` for all `x`. -/
protected def Function.Even {R R' : Type*} [Neg R] (f : R → R') : Prop := ∀ (x : R), f (-x) = f x

/-- A function is _odd_ if it satisfis `f (-x) = -f x` for all `x`. -/
protected def Function.Odd {R R' : Type*} [Neg R] [Neg R'] (f : R → R') : Prop :=
  ∀ (x : R), f (-x) = -(f x)

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure) -/
noncomputable def dft (Φ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  Fourier.fourierIntegral toCircle Measure.count Φ k

@[inherit_doc] scoped notation "𝓕" => dft

lemma dft_apply (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, toCircle (-(j * k)) • Φ j := by
  simp only [dft, Fourier.fourierIntegral_def, integral_countable' <| .of_finite ..,
    Measure.count_singleton, ENNReal.one_toReal, one_smul, tsum_fintype]

lemma dft_def (Φ : ZMod N → ℂ) : 𝓕 Φ = fun k ↦ ∑ j : ZMod N, toCircle (-(j * k)) • Φ j :=
  funext (dft_apply Φ)

lemma dft_neg (Φ : ZMod N → ℂ) : 𝓕 (fun j ↦ -(Φ j)) = fun k ↦ -(𝓕 Φ k) := by
  simp only [dft_def, smul_neg, sum_neg_distrib]

/-- Fourier inversion formula, discrete case. -/
lemma dft_dft (Φ : ZMod N → ℂ) : 𝓕 (𝓕 Φ) = fun j ↦ N * Φ (-j) := by
  ext1 j
  simp only [dft_def]
  change ∑ k, stdAddChar _ * ∑ l, stdAddChar _ * _ = _
  simp only [mul_sum, ← mul_assoc, ← AddChar.map_add_eq_mul, mul_comm _ j, ← neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_mul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, AddChar.map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact AddChar.sum_eq_zero_of_ne_one (AddChar.isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

section signs

lemma dft_comp_neg (Φ : ZMod N → ℂ) : 𝓕 (fun j ↦ Φ (-j)) = fun k ↦ 𝓕 Φ (-k) := by
  ext1 k
  simp only [dft_def]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ fun j ↦ by rw [Equiv.neg_apply, neg_mul_neg]

/-- The Fourier transform sends even functions to even functions. -/
lemma dft_even {Φ : ZMod N → ℂ} : Φ.Even ↔ (𝓕 Φ).Even := by
  have h {Φ : ZMod N → ℂ} (hΦ : Function.Even Φ) : Function.Even (𝓕 Φ) := by
    simp only [Function.Even, ← fun y ↦ congr_fun (dft_comp_neg Φ) y, funext fun y ↦ hΦ y,
      implies_true]
  refine ⟨h, fun hΦ x ↦ ?_⟩
  simpa only [neg_neg, mul_right_inj' (NeZero.ne (N : ℂ)), dft_dft] using h hΦ (-x)

/-- The Fourier transform sends odd functions to odd functions. -/
lemma dft_odd {Φ : ZMod N → ℂ} : Φ.Odd ↔ (𝓕 Φ).Odd := by
  have h {Φ : ZMod N → ℂ} (hΦ : Function.Odd Φ) : Function.Odd (𝓕 Φ) := by
    simp only [Function.Odd, ← fun y ↦ congr_fun (dft_comp_neg Φ) y, funext fun y ↦ hΦ y,
      dft_neg, implies_true]
  refine ⟨h, fun hΦ x ↦ ?_⟩
  simpa only [neg_neg, dft_dft, ← mul_neg, mul_right_inj' (NeZero.ne (N : ℂ))] using h hΦ (-x)

end signs

end ZMod

open ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma fourierTransform_eq_gaussSum_mulShift (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_def]
  refine congr_arg Finset.univ.sum (funext fun j ↦ ?_)
  rw [AddChar.mulShift_apply, mul_comm j, Submonoid.smul_def, smul_eq_mul, neg_mul,
    stdAddChar_apply, mul_comm (χ _)]

/-- For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a constant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum). -/
lemma fourierTransform_eq_inv_mul_gaussSum (k : ZMod N) (hχ : IsPrimitive χ) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter
