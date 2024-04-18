/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`completedHurwitzZetaEven a s = 1 / 2 * □ * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`completedCosZeta a s = □ * ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`

where `□` denotes a Gamma factor. Note that the term for `n = -a` in the first sum is omitted
if `a` is an integer, and the term for `n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function. We also define modified versions with a subscript `0`
which are entire functions differing from the above by multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems

* `completedHurwitzZetaEven`: the completed Hurwitz zeta function
* `completedCosZeta`: the completed cosine zeta function
* `differentiableAt_completedHurwitzZetaEven` and `differentiableAt_completedCosZeta`:
  differentiability away from `s = 0` and `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `completedHurwitzZetaEven_eq_tsum_int` and `completedCosZeta_eq_tsum_nat`: relation between the
  zeta functions and corresponding Dirichlet series for `1 < re s`
-/
noncomputable section

open Complex Filter Topology Asymptotics Real Set Classical MeasureTheory

/-!
## Differentiability and residues
-/

section FEPair
/--
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` (and also at
`s = 0` if `a ≠ 0`)
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0 ∨ a ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (completedHurwitzZetaEven a) s := by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
    (differentiableAt_id.div_const _)).div_const _
  · rw [div_ne_zero_iff, eq_true_intro two_ne_zero, and_true]
    refine Or.imp (by tauto) (fun ha ↦ ?_) hs
    simp only [hurwitzEvenFEPair, eq_false_intro ha, if_false]
  · change s / 2 ≠ ↑(1 / 2 : ℝ)
    rw [ofReal_div, ofReal_one, ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The difference of two completed even Hurwitz zeta functions is differentiable at `s = 1`. -/
lemma differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
    (a b : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ completedHurwitzZetaEven a s - completedHurwitzZetaEven b s) 1 := by
  have (s) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
  apply DifferentiableAt.sub
  · apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀
  · refine (differentiable_const _ _).div (differentiable_id _) one_ne_zero

lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (completedCosZeta a) s := by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rwa [div_ne_zero_iff, eq_true_intro two_ne_zero, and_true]
  · change s / 2 ≠ ↑(1 / 2 : ℝ) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h ↦ ?_) (fun ha ↦ ?_) hs'
    · simpa only [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simp_rw [eq_false_intro ha, if_false]

lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The residue of `completedHurwitzZetaEven a s` at `s = 1` is equal to `1`. -/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have h1 : Tendsto (fun s : ℂ ↦ (s - ↑(1  / 2 : ℝ)) * _) (𝓝[≠] ↑(1  / 2 : ℝ))
    (𝓝 ((1 : ℂ) * (1 : ℂ))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  have h2 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (1 / 2)) :=
    le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq 1)
  refine (h1.comp h2).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply]
  ring_nf

/-- The residue of `completedHurwitzZetaEven a s` at `s = 0` is equal to `-1` if `a = 0`, and `0`
otherwise. -/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedHurwitzZetaEven a s) (𝓝[≠] 0) (𝓝 (if a = 0 then -1 else 0)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : ℂ) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast, one_mul] at h1
  have h2 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] (0 / 2)) :=
    le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq 0)
  rw [zero_div] at h2
  refine (h1.comp h2).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply]
  ring_nf

lemma completedCosZeta_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedCosZeta a s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  have h2 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] (0 / 2)) :=
    le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq 0)
  rw [zero_div] at h2
  refine (h1.comp h2).congr (fun s ↦ ?_)
  rw [completedCosZeta, Function.comp_apply]
  ring_nf

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ - {0}`). -/
lemma hasSum_int_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2)
    (completedCosZeta a s) := by
  let c (n : ℤ) : ℂ := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    convert (hasSum_int_cosKernel₀ a ht).div_const 2 using 2 with n
    split_ifs with h <;> ring_nf
  simp_rw [← Int.cast_eq_zero (α := ℝ)] at hF
  convert hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_ using 1
  · simp only [c, Int.cast_eq_zero, ← Int.cast_abs, ofReal_intCast, div_right_comm, mul_div_assoc]
  · rw [mellin_div_const, completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_right two_pos]
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, norm_norm, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 ≤ |(i : ℝ)| ^ s.re), div_right_comm, le_rfl]

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ if n = 0 then 0 else Gammaℝ s * Real.cos (2 * π * a * n) / (n : ℂ) ^ s)
    (completedCosZeta a s) := by
  have hs' : s ≠ 0 := fun h ↦ (not_lt.mpr zero_le_one) (zero_re ▸ h ▸ hs)
    --fun h ↦ (zero_lt_one.trans hs).ne'
  have aux : ((|0| : ℤ) : ℂ) ^ s = 0 := by rw [abs_zero, Int.cast_zero, zero_cpow hs']
  convert (hasSum_int_completedCosZeta a hs).sum_nat_of_sum_int using 1 with n
  · ext1 n
    split_ifs with h
    · simp only [h, Nat.cast_zero, neg_zero, aux, div_zero, zero_div, zero_add]
    · simp only [ofReal_cos, Complex.cos, Nat.abs_cast, abs_neg, push_cast]
      ring_nf
  · rw [aux, div_zero, zero_div, add_zero]

/-- Formula for `completedHurwitzZetaEven` as a Dirichlet series in the convergence range. -/
lemma hasSum_int_completedHurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s / (↑|n + a| : ℂ) ^ s / 2) (completedHurwitzZetaEven a s) := by
  have hF (t : ℝ) (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n + a = 0 then 0
      else (1 / 2 : ℂ) * rexp (-π * (n + a) ^ 2 * t)) ((evenKernel a t - _) / 2) := by
    convert ofReal_sub _ _ ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const 2 using 2
    split_ifs
    · simp
    · ring_nf
  convert hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_ using 1
  · ext1 n
    ring_nf
  · simp_rw [mellin_div_const, apply_ite ofReal', ofReal_one, ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_right two_pos]
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]

/-!
## The un-completed even Hurwitz zeta
-/

/-- Technical lemma which will give us differentiability of Riemann zeta at `s = 0`. -/
lemma differentiableAt_update_of_residue
    {Λ : ℂ → ℂ} (hf : ∀ (s : ℂ) (_ : s ≠ 0) (_ : s ≠ 1), DifferentiableAt ℂ Λ s)
    {L : ℂ} (h_lim : Tendsto (fun s ↦ s * Λ s) (𝓝[≠] 0) (𝓝 L))
    (s : ℂ) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (Function.update (fun s ↦ Λ s / Gammaℝ s) 0 (L / 2)) s := by
  have claim (t) (ht : t ≠ 0) (ht' : t ≠ 1) : DifferentiableAt ℂ (fun u : ℂ ↦ Λ u / Gammaℝ u) t :=
    (hf t ht ht').mul differentiable_Gammaℝ_inv.differentiableAt
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case 2 : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp_rw [Function.update_noteq hx]
  -- now the hard case (Riemann zeta at `s = 0`)
  have c2 : Tendsto (fun s : ℂ ↦ Λ s / Gammaℝ s) (𝓝[≠] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div Gammaℝ_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    rw [Pi.div_apply, ← div_div, mul_div_cancel_left₀ _ hs]
  · -- The hard case: `s = 0`.
    simp_rw [← c2.limUnder_eq]
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht ↦ (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [Gammaℝ, zero_div, div_zero, Complex.Gamma_zero, mul_zero, cpow_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto c2 <| one_ne_zero' ℂ).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x ↦ by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' ↦ (hx <| inv_eq_zero.mp hx').elim

/-- The even part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`-/
noncomputable def hurwitzZetaEven (a : UnitAddCircle) :=
  Function.update (fun s : ℂ ↦ completedHurwitzZetaEven a s / Gammaℝ s)
  0 (if a = 0 then -1 / 2 else 0)

lemma hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : ℂ} (h : a ≠ 0 ∨ s ≠ 0) :
    hurwitzZetaEven a s = completedHurwitzZetaEven a s / Gammaℝ s := by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h | rfl
  · rw [Function.update_noteq h]
  · simp at h
    simp_rw [h, if_false, Function.update_same, Gammaℝ, zero_div, Complex.Gamma_zero, mul_zero,
      div_zero]

lemma hurwitzZetaEven_apply_zero (a : UnitAddCircle) :
    hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0 :=
  Function.update_same _ _ _

lemma hurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaEven (-a) s = hurwitzZetaEven a s := by
  simp_rw [hurwitzZetaEven, neg_eq_zero, completedHurwitzZetaEven_neg]

/-- The trivial zeroes of the even Hurwitz zeta function. -/
theorem hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaEven a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven, Function.update_noteq this,
    Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by rw [neg_mul, Nat.cast_add_one]⟩, div_zero]

/-- The Hurwitz zeta function is differentiable everywhere except at `s = 1`. This is true
even in the delicate case `a = 0` and `s = 0` (where the completed zeta has a pole, but this is
cancelled out by the Gamma factor). -/
lemma differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzZetaEven a) s := by
  have := differentiableAt_update_of_residue
    (fun t ht ht' ↦ differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this

lemma hurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have : Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s / Gammaℝ s) (𝓝[≠] 1) (𝓝 1) := by
    simpa only [Gammaℝ_one, inv_one, mul_one] using (completedHurwitzZetaEven_residue_one a).mul
      <| (differentiable_Gammaℝ_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp_rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]

lemma differentiableAt_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) 1 := by
  suffices DifferentiableAt ℂ
      (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s - 1 / (s - 1) / Gammaℝ s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven, Function.update_noteq hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (Gammaℝ _)]
  refine DifferentiableAt.mul ?_ differentiable_Gammaℝ_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_self, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
    <| (differentiableAt_const _).div differentiableAt_id one_ne_zero

/-- Expression for `hurwitzZetaEven a 1` as a limit. (Mathematically `hurwitzZetaEven a 1` is
undefined, but our construction assigns some value to it; this lemma is mostly of interest for
determining what that value is). -/
lemma tendsto_hurwitzZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) (𝓝 1)
    (𝓝 (hurwitzZetaEven a 1)) := by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto

/-- The difference of two even Hurwitz zeta functions is differentiable everywhere. -/
lemma differentiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaEven a s - hurwitzZetaEven b s) := by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert (differentiableAt_hurwitzZetaEven_sub_one_div a).sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using 2 with s
    abel

/--
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℤ`.
-/
lemma hasSum_int_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ 1 / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaEven a s) := by
  rw [hurwitzZetaEven, Function.update_noteq (not_lt.mpr zero_le_one <| zero_re ▸ · ▸ hs)]
  convert (hasSum_int_completedHurwitzZetaEven a hs).div_const (Gammaℝ s) using 2 with n
  simp only [div_right_comm _ _ (Gammaℝ _),
    div_self (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
lemma hasSum_nat_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (↑|n + a| : ℂ) ^ s + 1 / (↑|n + 1 - a| : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  convert (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one using 2 with n
  rw [add_div, ← abs_neg (n + 1 - a)]
  push_cast
  ring_nf

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s + 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  convert (hasSum_nat_hurwitzZetaEven a hs) <;>
  rw [_root_.abs_of_nonneg (by linarith [ha.1, ha.2])] <;>
  simp

/-!
## The un-completed cosine zeta
-/

/-- The cosine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), cos (2 * π * a * n) / n ^ s` for `1 < re s`. -/
noncomputable def cosZeta (a : UnitAddCircle) :=
  Function.update (fun s : ℂ ↦ completedCosZeta a s / Gammaℝ s) 0 (-1 / 2)

lemma cosZeta_apply_zero (a : UnitAddCircle) : cosZeta a 0 = -1 / 2 :=
  Function.update_same _ _ _

lemma cosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    cosZeta (-a) s = cosZeta a s := by
  simp_rw [cosZeta, completedCosZeta_neg]

/-- The trivial zeroes of the cosine zeta function. -/
theorem cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    cosZeta a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta, Function.update_noteq this,
    Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by rw [neg_mul, Nat.cast_add_one]⟩, div_zero]

/-- The cosine zeta function is differentiable everywhere, except at `s = 1` if `a = 0`. -/
lemma differentiableAt_cosZeta (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (cosZeta a) s := by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' ↦
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').mul
      (differentiable_Gammaℝ_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    simp_rw [cosZeta, Function.update_noteq hx, div_eq_mul_inv]

/-- If `a ≠ 0` then the cosine zeta function is entire. -/
lemma differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (cosZeta a) :=
  fun _ ↦ differentiableAt_cosZeta a (Or.inr ha)

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
lemma hasSum_int_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (cosZeta a s) := by
  rw [cosZeta, Function.update_noteq (not_lt.mpr zero_le_one <| zero_re ▸ · ▸ hs)]
  convert (hasSum_int_completedCosZeta a hs).div_const (Gammaℝ s) using 2 with n
  rw [mul_div_assoc _ (cexp _), div_right_comm _ (2 : ℂ),
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
lemma hasSum_nat_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.cos (2 * π * a * n) / (n : ℂ) ^ s) (cosZeta a s) := by
  have hs' : s ≠ 0 := (fun h ↦ (not_lt.mpr zero_le_one) ((zero_re ▸ h ▸ hs)))
  have := (hasSum_int_cosZeta a hs).sum_nat_of_sum_int
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg,
    abs_zero, Int.cast_zero, zero_cpow hs', div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.cos]
  convert this using 2 with n
  ring_nf

/-!
## Functional equations for the un-completed zetas
-/

/-- If `s` is not in `-ℕ`, and either `a ≠ 0` or `s ≠ 1`, then
`hurwitzZetaEven a (1 - s)` is an explicit multiple of `cosZeta s`. -/
lemma hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZetaEven a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * cosZeta a s := by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne, div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this, completedHurwitzZetaEven_one_sub, inv_Gammaℝ_one_sub hs, cosZeta,
    Function.update_noteq (by simpa using hs 0), Gammaℂ]
  ring_nf

/-- If `s` is not of the form `1 - n` for `n ∈ ℕ`, then `cosZeta a (1 - s)` is an explicit
multiple of `hurwitzZetaEven s`. -/
lemma cosZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    cosZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * hurwitzZetaEven a s := by
  rw [← Gammaℂ]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [cosZeta, Function.update_noteq, div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this, completedCosZeta_one_sub, inv_Gammaℝ_one_sub (fun n ↦ by simpa using hs (n + 1)),
    hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1)), Gammaℂ]
  ring_nf
