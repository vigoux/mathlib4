/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.DirichletFuncEq
import Mathlib.Analysis.NormedSpace.Connected

/-!
# L-series attached to periodic functions

We show that if `Φ` is a function `ZMod N → ℂ`, for a positive integer `N`, then `LSeries Φ` has
analytic continuation.

## Main definitions and results:

- Results about the un-completed L-series:

    * `congruenceLFunction`: the analytic continuation of the function `∑ n : ℕ, Φ n / n ^ s`,
      where `Φ` is a function `ZMod N → ℂ` for some `N : ℕ+`.
    * `congruenceLFunction_eq_LSeries`: the `congruenceLFunction` agrees with its Dirichlet series
      in the convergence range.
    * `differentiableAt_congruenceLFunction`: the function `congruenceLFunction Φ` is differentiable
      away from `s = 1`.
    * `differentiable_congruenceLFunction_of_sum_zero`: if `∑ j : ZMod N, Φ j = 0` then the
      L-function of `Φ` is entire.
    * `congruenceLFunction_one_sub`: the functional equation relating
      `L (1 - s, Φ)` and `L (s, 𝓕 Φ)` where `𝓕 Φ` is the discrete Fourier transform of `Φ`.

- Completed L-series (even part)

    * `completedCongruenceLFunctionEven`
    * `differentiableAt_completedCongruenceLFunctionEven`

- Completed L-series (odd part)

    * `completedCongruenceLFunctionOdd`
    * `differentiable_completedCongruenceLFunctionOdd`
-/

open Filter Topology Asymptotics HurwitzZeta Complex ZMod Finset
open scoped Nat Real

namespace DirichletContinuationOld

/-- The complement of a point is preconnected in `ℂ`.-/
lemma isPreconnected_compl_singleton (a : ℂ) : IsPreconnected ({a}ᶜ : Set ℂ) := by
  simp only [rank_real_complex, gt_iff_lt, Nat.one_lt_ofNat,
    isConnected_compl_singleton_of_one_lt_rank, IsConnected.isPreconnected]

/-- If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`. -/
lemma LSeriesSummable_coe_ZMod {N : ℕ+} (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (Complex.abs ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/-!
## The L-function attached to a periodic function
-/

/-- The analytic continuation of `∑' n : ℕ, Φ n / n ^ s` where `Φ` is periodic. -/
noncomputable def congruenceLFunction {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (ZMod.toAddCircle j) s

lemma congruenceLFunction_add {N : ℕ+} (Φ Ψ : ZMod N → ℂ) (s : ℂ) :
    congruenceLFunction (fun j ↦ Φ j + Ψ j) s =
    congruenceLFunction Φ s + congruenceLFunction Ψ s := by
  simp only [congruenceLFunction, add_mul, sum_add_distrib, mul_add]

lemma congruenceLFunction_mul {N : ℕ+} (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    congruenceLFunction (fun j ↦ a * Φ j) s = a * congruenceLFunction Φ s := by
  simp only [congruenceLFunction, mul_sum]
  congr 1 with j
  ring

lemma congruenceLFunction_sum {N : ℕ+} {ι : Type*} [Fintype ι]
    (Φ : ι → ZMod N → ℂ) (s : ℂ) :
    congruenceLFunction (fun j ↦ ∑ i, Φ i j) s = ∑ i, congruenceLFunction (Φ i) s := by
  simp only [congruenceLFunction, mul_sum, sum_mul, sum_comm (α := ZMod N)]

/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
lemma congruenceLFunction_eq_LSeries {N : ℕ+} (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    congruenceLFunction Φ s = LSeries (Φ ·) s := by
  rw [congruenceLFunction, LSeries, mul_sum,
    Nat.sumByResidueClasses (LSeriesSummable_coe_ZMod _ hs) N]
  refine sum_congr (by rfl) (fun j _ ↦ ?_) -- choose some `j ∈ ZMod N`
  have ha : (j.val / N : ℝ) ∈ Set.Icc 0 1 := ⟨by positivity, by
    rw [div_le_one (Nat.cast_pos.mpr N.pos), Nat.cast_le]
    exact (ZMod.val_lt _).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  congr 1 with m
  have aux0 : (m : ℂ) + ↑(j.val / N : ℝ) = ↑((j.val + N * m) / N : ℝ) := by
    push_cast
    field_simp
    ring
  have aux1 : (0 : ℝ) ≤ j.val + N * m := by positivity
  have aux2 : (0 : ℝ) ≤ (↑N)⁻¹ := by positivity
  have aux3 : arg (N : ℂ) ≠ π := by simpa only [natCast_arg] using Real.pi_pos.ne
  have aux4 : ((N : ℂ) ^ s)⁻¹ ≠ 0 := by simp
  rw [aux0, div_eq_mul_inv _ (N : ℝ), ofReal_mul, mul_cpow_ofReal_nonneg aux1 aux2, ← div_div,
    ofReal_inv, ofReal_natCast, cpow_neg, inv_cpow _ _ aux3, ← mul_div_assoc, mul_assoc,
    mul_div_cancel_left₀ _ aux4, mul_one_div, ← Nat.cast_mul, ← Nat.cast_add, ofReal_natCast,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), Nat.cast_add (R := ZMod _), Nat.cast_mul,
    CharP.cast_eq_zero (R := ZMod N) (p := N), zero_mul, add_zero]
  simp only [Nat.cast_add, natCast_val, Nat.cast_mul, cast_id', id_eq]

/-- The `L`-function of `Φ` is differentiable away from `s = 1`. -/
lemma differentiableAt_congruenceLFunction {N : ℕ+} (Φ : ZMod N → ℂ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (congruenceLFunction Φ) s := by
  refine (differentiable_neg.differentiableAt.const_cpow (by simp)).mul ?_
  exact DifferentiableAt.sum fun _ _ ↦ (differentiableAt_hurwitzZeta _ hs).const_mul _

/-- If `∑ Φ = 0`, then the `L`-function of `Φ` is entire. -/
lemma differentiable_congruenceLFunction_of_sum_zero {N : ℕ+} {Φ : ZMod N → ℂ}
    (hΦ : univ.sum Φ = 0) : Differentiable ℂ (congruenceLFunction Φ) := by
  -- strip off `N ^ (-s)` factor
  refine (differentiable_neg.const_cpow (by simp)).mul ?_
  -- rewrite as a sum of *differences* of Hurwitz zeta values
  have (s) : ∑ j : ZMod N, Φ j * hurwitzZeta (ZMod.toAddCircle j) s =
      ∑ j : ZMod N, Φ j * (hurwitzZeta (ZMod.toAddCircle j) s - hurwitzZeta 0 s) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hΦ, zero_mul, sub_zero]
  -- now apply `differentiable_hurwitzZeta_sub_hurwitzZeta`
  rw [funext this]
  exact Differentiable.sum fun i _ ↦ (differentiable_hurwitzZeta_sub_hurwitzZeta _ 0).const_mul _

/-- Compatibility between `expZeta` and a linear combination of Hurwitz zeta values.

This is less straightforward than it looks, since the relation is far from obvious from the
definition we use (as the Mellin transform of some kernel function). So we check that both sides
agree on the half-plane `{s : 1 < re s}`, and use uniqueness results for analytic functions.

TODO: investigate whether this can be "moved upstream", i.e. if we can formulate some nice relation
between the zeta kernels from which this relation would follow by taking Mellin transforms. -/
lemma expZeta_eq_congruenceLFunction {N : ℕ+} (j : ZMod N) (s : ℂ) (hs : s ≠ 1) :
    congruenceLFunction (fun k ↦ ZMod.toCircle (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  -- first reduce to equality in convergence range
  let U := {z : ℂ | z ≠ 1}
  let V := {z : ℂ | 1 < re z}
  have hUo : IsOpen U := isOpen_compl_singleton
  let f := congruenceLFunction (fun k ↦ ZMod.toCircle (j * k))
  let g := expZeta (ZMod.toAddCircle j)
  -- hypotheses for analytic-continuation argument
  have hf : AnalyticOn ℂ f U := by
    refine DifferentiableOn.analyticOn ?_ hUo
    exact fun u hu ↦ (differentiableAt_congruenceLFunction _ hu).differentiableWithinAt
  have hg : AnalyticOn ℂ g U := by
    refine DifferentiableOn.analyticOn ?_ hUo
    exact fun u hu ↦ (differentiableAt_expZeta _ _ (Or.inl hu)).differentiableWithinAt
  have hUc : IsPreconnected U := isPreconnected_compl_singleton 1
  have hV : V ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  -- apply uniqueness result to reduce to checking equality convergence range
  refine (hf.eqOn_of_preconnected_of_eventuallyEq hg hUc (show 2 ∈ U by simp [U]) ?_) hs
  -- now remains to prove equality on `1 < re s`
  filter_upwards [hV] with z hz
  dsimp only [f, g]
  rw [toAddCircle_apply, ← (hasSum_expZeta_of_one_lt_re (j.val / N) hz).tsum_eq,
    congruenceLFunction_eq_LSeries _ hz, LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hz), ofReal_div, ofReal_natCast,
    ofReal_natCast, mul_assoc, div_mul_eq_mul_div]
  have := ZMod.toCircle_intCast (N := N) (j.val * n)
  conv_rhs at this => rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc]
  rw [← this, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_zmod_val]

/-- Explicit formula for the congruence L-function of `𝓕 Φ`, where `𝓕` is the discrete Fourier
transform. -/
lemma congruenceLFunction_fourier {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1) :
    congruenceLFunction (𝓕 Φ) s =
    ∑ j : ZMod N, Φ j * expZeta (ZMod.toAddCircle (-j)) s := by
  simp only [← expZeta_eq_congruenceLFunction _ _ hs, ← congruenceLFunction_mul,
    ← congruenceLFunction_sum]
  congr 1 with j
  simp only [dft_def, mul_comm (Φ _), Submonoid.smul_def, smul_eq_mul, neg_mul]

/-- Functional equation for congruence L-functions, in terms of discrete Fourier transform. -/
lemma congruenceLFunction_one_sub {N : ℕ+} (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -↑n) (hs' : s ≠ 1) :
    congruenceLFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
      (cexp (π * I * s / 2) * congruenceLFunction (𝓕 Φ) s
       + cexp (-π * I * s / 2) * congruenceLFunction (𝓕 fun x ↦ Φ (-x)) s) := by
  rw [congruenceLFunction]
  simp only [hurwitzZeta_one_sub _ hs (Or.inr hs'), mul_assoc _ _ (Gamma s)]
  -- get rid of Gamma terms and power of N
  generalize (2 * π) ^ (-s) * Gamma s = C
  simp_rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc,
    neg_sub]
  congr 2
  -- now gather sum terms
  rw [congruenceLFunction_fourier _ _ hs', congruenceLFunction_fourier _ _ hs']
  conv_rhs => enter [2, 2]; rw [← (Equiv.neg _).sum_comp _ _ (by simp), Equiv.neg_apply]
  simp_rw [neg_neg, mul_sum, ← sum_add_distrib, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← mul_add, map_neg, add_comm]

section parity

/-!
## Completed L-series

We give two different definitions of a completed L-series for a function `Φ : ZMod N → ℂ`: an
"even" completed L-series and an "odd" one. These differ in the Gamma-factors appearing.
-/

/-- The even part of the completed congruence zeta function. This is 0 if `Φ` is odd. -/
noncomputable def completedCongruenceLFunctionEven {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven (ZMod.toAddCircle j) s

lemma completedCongruenceLFunctionEven_comp_neg {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) :
    completedCongruenceLFunctionEven (fun j ↦ Φ (-j)) s =
    completedCongruenceLFunctionEven Φ s := by
  unfold completedCongruenceLFunctionEven
  rw [← (Equiv.neg _).sum_comp _ _ (by simp)]
  congr 2 with j
  simp [completedHurwitzZetaEven_neg]

/-- If `Φ` is odd, then `completedCongruenceLFunctionEven Φ` is identically 0. -/
lemma completedCongruenceLFunctionEven_eq_zero {N : ℕ+} {Φ : ZMod N → ℂ}
    (hΦ : ∀ j : ZMod N, Φ (-j) = -Φ j) (s : ℂ) :
    completedCongruenceLFunctionEven Φ s = 0 := by
  rw [← eq_neg_self_iff]
  conv_lhs => rw [← completedCongruenceLFunctionEven_comp_neg]
  simp_rw [hΦ, completedCongruenceLFunctionEven, neg_mul, sum_neg_distrib, mul_neg]

/-- The even completed congruence zeta function is analytic except for poles at `s = 0` if
`Φ 0 ≠ 0`, and at `s = 1` if `∑ j, Φ j ≠ 0`. (This result is optimal.) -/
lemma differentiableAt_completedCongruenceLFunctionEven {N : ℕ+} {Φ : ZMod N → ℂ} {s : ℂ}
    (hs₀ : s ≠ 0 ∨ Φ 0 = 0) (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (completedCongruenceLFunctionEven Φ) s := by
  refine (differentiable_neg.const_cpow (by simp)).differentiableAt.mul ?_
  rcases eq_or_ne s 1 with rfl | hs
  · -- s = 1 : need to rearrange sum
    have (s) : ∑ j : ZMod ↑N, Φ j * completedHurwitzZetaEven (ZMod.toAddCircle j) s =
        ∑ j : ZMod ↑N, Φ j * (completedHurwitzZetaEven (ZMod.toAddCircle j) s
        - completedHurwitzZetaEven 0 s) := by
      simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, (by tauto : ∑ j : ZMod ↑N, Φ j = 0),
        zero_mul, sub_zero]
    rw [funext this]
    refine .sum fun j _ ↦ (differentiableAt_const _).mul ?_
    apply differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
  · -- s ≠ 1 : show each summand is differentiable
    refine .sum fun j _ ↦ ?_
    rcases eq_or_ne s 0 with rfl | hs'
    · -- s = 0 case : need to handle j = 0 separately
      rcases eq_or_ne j 0 with rfl | hj
      · simpa only [show Φ 0 = 0 by tauto, zero_mul] using differentiableAt_const _
      · apply (differentiableAt_const _).mul
        refine differentiableAt_completedHurwitzZetaEven _ (Or.inr fun h ↦ ?_) zero_ne_one
        exact ((map_zero (ZMod.toAddCircle (N := N))) ▸ (ZMod.toAddCircle_injective N).ne hj) h
    · exact (differentiableAt_completedHurwitzZetaEven _ (Or.inl hs') hs).const_mul _

/-- The odd part of the completed congruence zeta function. This is 0 if `Φ` is even. -/
noncomputable def completedCongruenceLFunctionOdd {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s

lemma completedCongruenceLFunctionOdd_comp_neg {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) :
    completedCongruenceLFunctionOdd (fun j ↦ Φ (-j)) s =
    -completedCongruenceLFunctionOdd Φ s := by
  unfold completedCongruenceLFunctionOdd
  congr 1
  rw [← (Equiv.neg (ZMod N)).sum_comp _ _ (by simp), ← mul_neg, ← sum_neg_distrib]
  congr 2 with j
  simp [completedHurwitzZetaOdd_neg]

lemma differentiable_completedCongruenceLFunctionOdd {N : ℕ+} (Φ : ZMod N → ℂ) :
    Differentiable ℂ (completedCongruenceLFunctionOdd Φ) := by
  refine (differentiable_neg.const_cpow (by simp)).mul ?_
  exact Differentiable.sum fun j _ ↦ (differentiable_completedHurwitzZetaOdd _).const_mul _

/-- If `Φ` is even, then `completedCongruenceLFunctionOdd Φ` is identically 0. -/
lemma completedCongruenceLFunctionOdd_eq_zero {N : ℕ+} {Φ : ZMod N → ℂ}
    (hΦ : ∀ j : ZMod N, Φ (-j) = Φ j) (s : ℂ) :
    completedCongruenceLFunctionOdd Φ s = 0 := by
  simp_rw [← eq_neg_self_iff, ← completedCongruenceLFunctionOdd_comp_neg, hΦ]

/-- The un-completed L-function can be recovered from the completed ones, up to a minor grain
of salt at `s = 0`. -/
lemma congruenceLFunction_eq_completed {N : ℕ+} (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    congruenceLFunction Φ s = completedCongruenceLFunctionEven Φ s / Gammaℝ s +
    completedCongruenceLFunctionOdd Φ s / Gammaℝ (s + 1) := by
  rw [completedCongruenceLFunctionOdd, completedCongruenceLFunctionEven,
    mul_div_assoc, mul_div_assoc, ← mul_add, sum_div, sum_div,
    ← sum_add_distrib, congruenceLFunction]
  congr 2 with j
  by_cases h : j ≠ 0 ∨ s ≠ 0
  · rw [hurwitzZeta, hurwitzZetaOdd, mul_add, mul_div_assoc, mul_div_assoc,
      hurwitzZetaEven_def_of_ne_or_ne]
    rw [← map_zero (ZMod.toAddCircle (N := N))]
    refine h.imp (ZMod.toAddCircle_injective N).ne id
  · simp_rw [(by tauto : j = 0), (by tauto : Φ 0 = 0), zero_mul, zero_div, zero_add]

end parity
