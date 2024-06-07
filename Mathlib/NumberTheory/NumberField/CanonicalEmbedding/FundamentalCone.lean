/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.NumberTheory.NumberField.Units.Regulator


-- import Mathlib.Sandbox

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂`
that is a fundamental domain for the action of `(𝓞 K)ˣ` up to roots of unity.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset stable
by multiplication by a real number, see `smul_mem_of_mem`--, that is also a fundamental domain
for the action of `(𝓞 K)ˣ` up to roots of unity, see `exists_unitSMul_me` and
`torsion_unitSMul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPoint`: the subset of elements of the
fundamental cone that are images of algebraic integers of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPointEquiv`: the equivalence between
`fundamentalCone.integralPoint K` and the principal non-zero ideals of `𝓞 K` times the
torsion of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_eq`: the number of principal
non-zero ideals in `𝓞 K` of norm `n` multiplied by the number of roots of unity is
equal to the number of `fundamentalCone.integralPoint K` of norm `n`.

## Tags

number field, canonical embedding, principal ideals
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by multiplication component
by component with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (E K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

variable [NumberField K]

theorem unitSMul_eq_iff_mul_eq {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : E K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

theorem unitSMul_eq_zero (u : (𝓞 K)ˣ) (x : E K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · have := congr_fun (congr_arg Prod.fst h) w
      rw [unitSMul_smul, Prod.fst_mul, Pi.mul_apply, Prod.fst_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp)
    · have := congr_fun (congr_arg Prod.snd h) w
      rw [unitSMul_smul, Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp)
  · rw [h, smul_zero]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional

variable [NumberField K] {K}

open Classical in
/-- The map from `ℝ^r₁ × ℂ^r₂` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` (with `w₀` a fixed place)
defined in such way that: 1) it factors the map `logEmbedding`, see `logMap_eq_logEmbedding`;
2) it is constant on the lines `{c • x | c ∈ ℝ}`, see `logMap_smul`. -/
def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

@[simp]
theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  rw [logMap, map_zero, map_zero, Real.log_zero, zero_mul, sub_self, mul_zero, Pi.zero_apply]

theorem logMap_mul {x y : E K} (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  rw [map_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, mixedEmbedding.norm_unit, Real.log_one, zero_mul, sub_zero, normAtPlace_apply,
    logEmbedding_component]

theorem logMap_unitSMul (u : (𝓞 K)ˣ) {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_torsion_unitSMul (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

theorem logMap_smul {x : E K} (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  · ext
    have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
    simp_rw [logMap, normAtPlace_real, norm_real, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
      sub_self, zero_mul, Pi.zero_apply]
  · rw [norm_real]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)

@[simp]
theorem logMap_apply_of_norm_one {x : E K} (hx : mixedEmbedding.norm x = 1) {w : InfinitePlace K}
    (hw : w ≠ w₀) :
    logMap x ⟨w, hw⟩ = mult w * Real.log (normAtPlace w x) := by
  rw [logMap, hx, Real.log_one, zero_mul, sub_zero]

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem nonZeroDivisors BigOperators

variable [NumberField K]

open Classical in
/-- The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (E K) :=
  logMap⁻¹' (Zspan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _)) \
      {x | mixedEmbedding.norm x = 0}

namespace fundamentalCone

variable {K}

theorem norm_pos_of_mem {x : E K} (hx : x ∈ fundamentalCone K) :
    0 < mixedEmbedding.norm x :=
  lt_iff_le_and_ne.mpr ⟨mixedEmbedding.norm_nonneg _, Ne.symm hx.2⟩

theorem normAtPlace_pos_of_mem {x : E K} (hx : x ∈ fundamentalCone K) (w : InfinitePlace K) :
    0 < normAtPlace w x :=
  lt_iff_le_and_ne.mpr ⟨normAtPlace_nonneg _ _,
    (mixedEmbedding.norm_ne_zero_iff.mp (ne_of_gt (norm_pos_of_mem hx)) w).symm⟩

theorem smul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

theorem smul_mem_iff_mem {x : E K} {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_of_mem h hc⟩
  convert smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

theorem exists_unitSMul_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unitSMul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_torsion_unitSMul _ hζ]
    exact hx.1
  · simpa only [unitSMul_smul, Set.mem_setOf_eq, map_mul, norm_eq_norm, Rat.cast_abs, mul_eq_zero,
    abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff, RingOfIntegers.coe_eq_zero_iff,
    Units.ne_zero, false_or] using hx.2

theorem unitSMul_mem_iff_mem_torsion {x : E K} (hx : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact Submodule.zero_mem _
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unitSMul _ hx.2]
      exact h.1
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      exact hx.1
  · exact torsion_unitSMul_mem_of_mem hx h

variable (K) in
theorem measurableSet :
    MeasurableSet (fundamentalCone K) := by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
    refine MeasurableSet.preimage (Zspan.fundamentalDomain_measurableSet _) <|
      measurable_pi_iff.mpr fun w ↦ measurable_const.mul ?_
    exact (continuous_normAtPlace _).measurable.log.sub <|
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

section normLessOne

variable (K)

abbrev normLessThanOne : Set (E K) := {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

abbrev normEqOne : Set (E K) := {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = 1}

open Pointwise FiniteDimensional Bornology MeasureTheory Filter

theorem smul_normEqOne {c : ℝ} (hc : 0 < c) :
    c • normEqOne K = {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = c ^ finrank ℚ K} := by
  ext
  rw [← Set.preimage_smul_inv₀ (ne_of_gt hc), Set.preimage_setOf_eq, Set.mem_setOf_eq,
    mixedEmbedding.norm_smul, abs_inv, abs_eq_self.mpr hc.le, inv_pow, mul_comm, mul_inv_eq_one₀
    (pow_ne_zero _ (ne_of_gt hc)), Set.mem_setOf_eq, and_congr_left_iff]
  exact fun _ ↦ smul_mem_iff_mem (inv_ne_zero (ne_of_gt hc))

variable {K} in
theorem exists_mem_smul_normEqOne {x : E K} (hx : x ∈ normLessThanOne K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ x ∈ c • normEqOne K := by
  have h₁ : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  have h₂ : 0 < mixedEmbedding.norm x ^ (finrank ℚ K : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (norm_pos_of_mem hx.1) _
  refine ⟨(mixedEmbedding.norm x) ^ (finrank ℚ K : ℝ)⁻¹, h₂, ?_, ?_⟩
  · exact Real.rpow_le_one (mixedEmbedding.norm_nonneg _) hx.2 (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [smul_normEqOne K h₂]
    refine ⟨hx.1, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mixedEmbedding.norm_nonneg _), inv_mul_cancel h₁,
      Real.rpow_one]

theorem smul_normEqOne_subset {c : ℝ} (hc₁ : 0 < c) (hc₂ : c ≤ 1) :
    c • normEqOne K ⊆ normLessThanOne K := by
  rw [smul_normEqOne K hc₁]
  refine fun x hx ↦ ⟨hx.1, ?_⟩
  rw [hx.2]
  exact pow_le_one _ hc₁.le hc₂

theorem isBounded_normEqOne :
    IsBounded (normEqOne K) := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_closedBall_lt 0 0
  have h₁ : ∀ ⦃x w⦄, x ∈ normEqOne K → w ≠ w₀ → |mult w * Real.log (normAtPlace w x)| ≤ r := by
    intro x w hx hw
    rw [← logMap_apply_of_norm_one hx.2]
    suffices ‖logMap x‖ ≤ r by exact (pi_norm_le_iff_of_nonneg hr₁.le).mp this ⟨w, hw⟩
    exact mem_closedBall_zero_iff.mp (hr₂ hx.1.1)
  have h₂ : ∀ ⦃x⦄, x ∈ normEqOne K → mult (w₀ : InfinitePlace K) * Real.log (normAtPlace w₀ x) ≤
      (Finset.univ.erase w₀).card • r := by
    intro x hx
    suffices mult (w₀ : InfinitePlace K) * Real.log (normAtPlace w₀ x) =
        - ∑ w ∈ Finset.univ.erase w₀, mult w * Real.log (normAtPlace w x) by
      rw [this, ← Finset.sum_neg_distrib, ← Finset.sum_const]
      exact Finset.sum_le_sum fun w hw ↦
        neg_le_of_neg_le (abs_le.mp (h₁ hx (Finset.mem_erase.mp hw).1)).1
    simp_rw [← Real.log_pow]
    rw [← add_eq_zero_iff_eq_neg, Finset.univ.add_sum_erase (fun w ↦
      ((normAtPlace w x) ^ mult w).log) (Finset.mem_univ w₀), ← Real.log_prod,
      ← mixedEmbedding.norm_apply, hx.2, Real.log_one]
    exact fun w _ ↦  pow_ne_zero _ <| ne_of_gt (normAtPlace_pos_of_mem hx.1 w)
  have h₃ : ∀ ⦃x w c⦄, 0 ≤ c → x ∈ fundamentalCone K →
      mult w * Real.log (normAtPlace w x) ≤ c → normAtPlace w x ≤ Real.exp c := by
    intro x w c hc hx
    rw [← le_div_iff' (Nat.cast_pos.mpr mult_pos),
      Real.log_le_iff_le_exp (normAtPlace_pos_of_mem hx w)]
    exact fun h ↦ le_trans h <| Real.exp_le_exp.mpr (div_le_self hc one_le_mult)
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr
    ⟨max (Real.exp r) (Real.exp ((Finset.univ.erase (w₀ : InfinitePlace K)).card • r)),
      fun x hx ↦ mem_closedBall_zero_iff.mpr ?_⟩
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ ↦ ?_
  by_cases hw : w = w₀
  · rw [hw]
    exact (h₃ (nsmul_nonneg (hr₁.le) _) hx.1 (h₂ hx)).trans (le_max_right _ _)
  · exact le_trans (h₃ hr₁.le hx.1 (abs_le.mp (h₁ hx hw)).2) (le_max_left _ _)

theorem isBounded_normLessThanOne :
    IsBounded (normLessThanOne K) := by
  classical
  obtain ⟨r, hr₁, hr₂⟩ := (isBounded_normEqOne K).subset_ball_lt 0 0
  refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨r, fun x hx ↦ ?_⟩
  obtain ⟨c, hc₁, _, hc₂⟩ := exists_mem_smul_normEqOne hx
  suffices x ∈ c • Metric.ball (0 : (E K)) r by
    rw [smul_ball (ne_of_gt hc₁), smul_zero] at this
    refine Set.mem_of_subset_of_mem (Metric.ball_subset_ball ?_) this
    rwa [mul_le_iff_le_one_left hr₁, Real.norm_eq_abs, abs_eq_self.mpr hc₁.le]
  exact (Set.image_subset _ hr₂) hc₂

theorem frontier_normLessThanOne :
    frontier (normLessThanOne K) ⊆ frontier (fundamentalCone K) ∪ normEqOne K := by
  rw [show normLessThanOne K = fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1} by ext; simp]
  refine le_trans (frontier_inter_subset _ _) ?_
  intro x hx
  cases hx with
  | inl h =>
      left
      exact Set.mem_of_mem_inter_left h
  | inr h =>
      rw [show frontier {x | mixedEmbedding.norm x ≤ 1} = {x | mixedEmbedding.norm x = 1} by sorry]
        at h
      by_cases hx : x ∈ fundamentalCone K
      · right
        refine ⟨hx, h.2⟩
      · left
        have : x ∉ interior (fundamentalCone K) := by
          by_contra h
          exact hx <| interior_subset h
        refine ⟨h.1, this⟩

theorem measurableSet_normEqOne :
    MeasurableSet (normEqOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

-- To prove that the frontier of `X` is of measure zero?
-- MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero

abbrev normLessThanOne₀ : Set (E K) :=
    {x | x ∈ normLessThanOne K ∧ ∀ w, (hw : IsReal w) → x.1 ⟨w, hw⟩ ≥ 0}

open Classical

theorem volume_normLessOne :
    volume (normLessThanOne K) = 2 ^ (NrRealPlaces K) * volume (normLessThanOne₀ K) := by
  sorry

def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def normUnits : {w : InfinitePlace K // w ≠ w₀} → ((InfinitePlace K) → ℝ) :=
  fun i w ↦ w (fundSystem K (equivFinRank K i)) ^ mult w

theorem normUnits_pos (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    0 < normUnits K i w := sorry

def normUnitsEval₀ (i w : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
  fun x ↦ if hi : i = w₀ then x w₀ else normUnits K ⟨i, hi⟩ w ^ (x i)

def FDeriv_normUnitsEval₀ (i w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    (InfinitePlace K → ℝ) →L[ℝ] ℝ := by
  exact if hi : i = w₀ then ContinuousLinearMap.proj w₀ else
    (normUnitsEval₀ K i w x * (normUnits K ⟨i, hi⟩ w).log) • ContinuousLinearMap.proj i

theorem hasFDeriv_normUnitsEval₀ (i w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    HasFDerivAt (normUnitsEval₀ K i w) (FDeriv_normUnitsEval₀ K i w x) x := by
  unfold normUnitsEval₀
  unfold FDeriv_normUnitsEval₀
  split_ifs
  · exact hasFDerivAt_apply w₀ x
  · unfold normUnitsEval₀
    rw [dif_neg]
    exact HasFDerivAt.const_rpow (hasFDerivAt_apply i x) (normUnits_pos K _ _)

def normUnitsEval : (InfinitePlace K → ℝ) → InfinitePlace K → ℝ :=
  fun x w ↦ ∏ i, normUnitsEval₀ K i w x

def prodNormUnitsEval (w : InfinitePlace K) (c : InfinitePlace K → ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase w₀, normUnitsEval₀ K i w c

def jacobianCoeff (w i : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
    fun c ↦ if hi : i = w₀ then 1 else (c w₀) * normUnits K ⟨i, hi⟩ w

def jacobian : (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) →L[ℝ] InfinitePlace K → ℝ := by
  intro c
  refine ContinuousLinearMap.pi ?_
  intro i
  exact (prodNormUnitsEval K i c • ∑ w, (jacobianCoeff K i w c) • ContinuousLinearMap.proj w)

theorem jacobian_det (c : InfinitePlace K → ℝ) :
    (jacobian K c).det = 1 := by
  have : LinearMap.toMatrix' (jacobian K c) =
      Matrix.of fun i w ↦ prodNormUnitsEval K i c * jacobianCoeff K i w c := by
    ext; simp [jacobian]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', this]
  rw [Matrix.det_mul_column]
  
  sorry

#exit

abbrev normLessThanOne₁ : Set ((InfinitePlace K) → ℝ) :=
  normUnitsEval K '' (Set.univ.pi fun _ ↦ Set.Ico 0 1)

theorem volume_normLessOne₀ :
    volume (normLessThanOne₀ K) =
      (2 * NNReal.pi) ^ (NrRealPlaces K) * volume (normLessThanOne₁ K) := by
  sorry

-- def jacobian_normUnitsEval :
--     (InfinitePlace K → ℝ) → Matrix (InfinitePlace K) (InfinitePlace K) ℝ :=
--   fun c ↦
--     Matrix.of fun i w : InfinitePlace K ↦
--       if hi : i = w₀ then normUnitsEval₀ K c w else
--         (c w₀) * (normUnits K ⟨i, hi⟩ w).log * normUnitsEval₀ K c w

-- example : (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ := by
--   exact Fintype.total ℝ ℝ

-- def lin (c : InfinitePlace K → ℝ) (w : InfinitePlace K) : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ := by
--   refine Fintype.total ℝ ℝ ?_
--   intro i
--   exact if hi : i = w₀ then normUnitsEval₀ K c w else
--         (c w₀) * (normUnits K ⟨i, hi⟩ w).log * normUnitsEval₀ K c w

-- def fDeriv_normUnitsEval :
--     (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) →L[ℝ] (InfinitePlace K → ℝ) := by
--   intro c
--   refine ContinuousLinearMap.pi ?_
--   intro i

--   exact LinearMap.toContinuousLinearMap (lin K c i)

theorem hasFDeriv_normUnitsEval (c : InfinitePlace K → ℝ) :
    HasFDerivAt (𝕜 := ℝ) (normUnitsEval K) (jacobian K c) c := by
  rw [hasFDerivAt_pi']
  intro w
  simp_rw [normUnitsEval]
  have t₀ := fun i ↦ hasFDeriv_normUnitsEval₀ K i w c
  have := HasFDerivAt.finset_prod (u := Finset.univ) (fun i _ ↦ t₀ i)
  simp at this
  -- unfold FDeriv_normUnitsEval₀ at this
  -- simp at this
  convert this
  rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ w₀)]
  rw [Finset.sum_subtype (p := fun x ↦ x ≠ w₀)]
  unfold FDeriv_normUnitsEval₀
  simp_rw [Subtype.coe_eta, dite_eq_ite, smul_ite, dif_pos]
  rw [Finset.univ.sum_ite_of_false]
  simp_rw [smul_smul, ← mul_assoc]
  simp_rw [Finset.univ.prod_erase_mul _ sorry]
  simp_rw [← smul_smul]
  rw [← Finset.smul_sum]
  rw [← Finset.univ.prod_erase_mul _ (Finset.mem_univ w₀)]
  rw [← smul_smul]
  rw [Finset.smul_sum]
  unfold jacobian
  rw [ContinuousLinearMap.proj_pi]
  unfold jacobianCoeff
  unfold prodNormUnitsEval
  rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ w₀)]
  rw [dif_pos rfl]
  ext
  rw [one_smul]
  rw [smul_add]
  congr 3
  sorry
  sorry
  sorry



#exit

  rw [Finset.sum_subtype (p := fun x ↦ x ≠ w₀)] at this
  · unfold FDeriv_normUnitsEval₀ at this
    simp_rw [Subtype.coe_eta, dite_eq_ite, smul_ite] at this
    simp_rw [dif_pos] at this
    rw [Finset.univ.sum_ite_of_false] at this

    simp_rw [← mul_smul_comm] at this
--    simp only [ne_eq, smul_ite, ↓reduceDite] at this
--    simp only [ne_eq, Subtype.coe_eta, dite_eq_ite, smul_ite, ↓reduceDite] at this

    sorry
  · refine fun x ↦ ⟨fun hx ↦ Finset.ne_of_mem_erase hx,
      fun hx ↦ Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩




#exit

  rw [show ∑ x ∈ Finset.univ.erase w₀, (∏ j ∈ Finset.univ.erase x, normUnitsEval₀ K j w c) •
    FDeriv_normUnitsEval₀ K x w c = ∑ x ∈ Finset.univ.erase w₀, (∏ j ∈ Finset.univ.erase x,
    normUnitsEval₀ K j w c) • ((normUnitsEval₀ K x w c * (normUnits K ⟨x, ?_⟩ w).log) •
    ContinuousLinearMap.proj x) by sorry] at this

#exit


  rw [show (∑ x ∈ Finset.univ.erase (w₀ : InfinitePlace K), if h : x = w₀ then
    (∏ j ∈ Finset.univ.erase x, normUnitsEval₀ K j w c) • ContinuousLinearMap.proj w₀ else
    (∏ j ∈ Finset.univ.erase x, normUnitsEval₀ K j w c) •
        (normUnitsEval₀ K x w c * (normUnits K ⟨x, h⟩ w).log) • ContinuousLinearMap.proj x) = 0
    by sorry] at this


  rw [Finset.sum_dite_of_false (fun x hx ↦ Finset.ne_of_mem_erase hx)] at this
  simp at this
  rw [Finset.sum_attach] at this


#exit

  rw [Finset.sum_congr rfl ?_] at this
  · sorry
  · sorry
  · intro x hx
    rw [dif_neg (Finset.ne_of_mem_erase hx)]

#exit

  rw [Finset.sum_dite_of_false] at this
  · simp at this
    sorry
  · intro x hx
    exact Finset.ne_of_mem_erase hx
  ·



#exit

  rw [fDeriv_normUnitsEval]
  rw [hasFDerivAt_pi']
  intro w
  simp only [normUnitsEval, Pi.smul_apply, smul_eq_mul]
  simp only [lin]
  rw [ContinuousLinearMap.proj_pi]
  rw [LinearMap.pi_apply_eq_sum_univ]
  rw [map_sum]
  simp only [dite_smul]
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ w₀)]
  rw [dif_pos rfl]

--  rw [Finset.sum_apply_dite]
--  simp [Finset.filter_eq]

#exit

  let F := InfinitePlace K → ℝ
  have := @hasFDerivAt_single ℝ (InfinitePlace K) _ _ _ (fun _ ↦ ℝ) _ _ w₀
  have : HasFDerivAt (fun x : F ↦ x w₀)
    (ContinuousLinearMap.pi (Pi.single w (ContinuousLinearMap.id ℝ _))) c := sorry

#exit


  refine hasFDerivAt_pi'' ?_
  intro w
  simp [fDeriv_normUnitsEval, ContinuousLinearMap.proj_pi]
  let F := InfinitePlace K → ℝ
  have : HasFDerivAt (fun x : F ↦ x w₀) _ x := sorry

  simp [fDeriv_normUnitsEval, jacobian_normUnitsEval, Finset.prod_apply, Pi.pow_apply,
    Real.log_pow, Matrix.toLin'_apply', ContinuousLinearMap.proj_pi]
  simp [normUnitsEval]

  let F := InfinitePlace K → ℝ
  have : HasFDerivAt (fun x : F ↦ x w₀)
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id 𝕜 (E i)))) x := sorry





#exit
  split_ifs

theorem volume_normLessOne₁ :
    (volume (normLessThanOne₁ K)).toReal = regulator K := by
  let s : Set (InfinitePlace K → ℝ) := Set.univ.pi fun _ ↦ Set.Ico 0 1
  have hs : MeasurableSet s := sorry
  have hf₁ : Set.InjOn (normUnitsEval K) s := sorry
  have hf₂ : Measurable (normUnitsEval K) := sorry
  have hf₃ : ∀ x ∈ s, HasFDerivWithinAt (normUnitsEval K) (fDeriv_normUnitsEval K x) s x := sorry
  have t₀ := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf₃ hf₁ (fun _ ↦ 1)
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul,
    mul_one] at t₀
  rw [t₀]




#exit

  Set.range (fun v : (InfinitePlace K) → Set.Ico 0 1 ↦ Π i : Fin (rank K), (normUnits K i)
    )
theorem normLessThanOne₂
example {ι : Type*} [Fintype ι] (u : ι → (ι → ℝ)) : sorry := by
  let s : Set (ι → ℝ) := Set.univ.pi fun _ ↦ Set.Ico 0 1
  let f : (ι → ℝ) → (ι → ℝ) := by
    intro a
    exact ∏ i, (u i) ^ (a i)


#exit

example : 0 = 1 := by
  classical
  let E₀ := Fin (rank K) → ℝ
  let u : Fin (rank K) → E₀ := sorry
  let s : Set (Fin (rank K) → ℝ) := Set.univ.pi fun _ ↦ Set.Ico 0 1
  let f : E₀ → E₀ := by
    intro x i
    exact ∏ j, (u j) i ^ x i
  have hs : MeasurableSet s := sorry
  --  Real.hasStrictDerivAt_const_rpow
  let f' : E₀ → E₀ →L[ℝ] E₀ := by
    intro x
    refine ⟨⟨⟨?_, sorry⟩, sorry⟩, sorry⟩
    intro y i
    exact ((u i) ^ (x i) * Real.log (u i)) * y i
  have hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x := sorry
  have hf : Set.InjOn f s := sorry
  have h'f : Measurable f := sorry
  let g : E₀ → ENNReal := fun _ ↦ 1
  have t₀ := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hf g
  simp [g] at t₀
  let R : ℝ := sorry
  have t₁ : ∀ x, (f' x).det = R := sorry
  simp_rw [t₁] at t₀
  simp at t₀



#exit

def gen : Fin (rank K) → (E K) := by
  intro i
  let ε := mixedEmbedding K (fundSystem K i)
  refine ⟨?_, ?_⟩
  · intro w
    exact normAtPlace w.val ε
  · intro w
    exact (normAtPlace w.val ε : ℂ)

theorem normAtPlace_gen (w : InfinitePlace K) (i : Fin (rank K)) :
    normAtPlace w (gen i) = w (fundSystem K i) := by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_isReal hw, gen, normAtPlace_apply, Real.norm_eq_abs,
      abs_eq_self.mpr (apply_nonneg _ _)]
  · simp_rw [normAtPlace_apply_isComplex hw, gen, normAtPlace_apply, Complex.norm_eq_abs,
      Complex.abs_ofReal, abs_eq_self.mpr (apply_nonneg _ _)]

theorem norm_gen (i : Fin (rank K)) :
    mixedEmbedding.norm (gen i) = 1 := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_gen, prod_eq_abs_norm, show
    |(Algebra.norm ℚ) (fundSystem K i : K)| = 1 by exact isUnit_iff_norm.mp (fundSystem K i).isUnit,
    Rat.cast_one]

theorem logMap_gen (i : Fin (rank K)) :
    logMap (gen i) = logEmbedding K (fundSystem K i) := by
  ext
  rw [logMap_apply_of_norm_one (norm_gen i), normAtPlace_gen, logEmbedding_component]

variable (K) in
def Ξ : Set (E K) := {x : E K | ∀ w, normAtPlace w x = 1}

theorem normAtPlace_of_mem_Xi (w : InfinitePlace K) {x : E K} (hx : x ∈ Ξ K) :
    normAtPlace w x = 1 := hx w

theorem norm_one_of_mem_Xi {x : E K} (hx : x ∈ Ξ K) :
    mixedEmbedding.norm x = 1 := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_of_mem_Xi _ hx, one_pow, Finset.prod_const_one]

theorem logMap_of_mem_Xi {x : E K} (hx : x ∈ Ξ K) :
    logMap x = 0 := by
  ext
  simp_rw [logMap_apply_of_norm_one (norm_one_of_mem_Xi hx), normAtPlace_of_mem_Xi _ hx,
    Real.log_one, mul_zero, Pi.zero_apply]

theorem logMap_eq_logMap_iff {x y : E K} (hx : mixedEmbedding.norm x = 1)
    (hy : mixedEmbedding.norm y = 1) :
    logMap x = logMap y ↔ ∃ ξ ∈ Ξ K, x = ξ * y := by
  refine ⟨?_, ?_⟩
  · intro h
    have : ∀ w, w ≠ w₀ → normAtPlace w x = normAtPlace w y := by
      intro w hw
      have := congr_fun h ⟨w, hw⟩
      rw [logMap_apply_of_norm_one hx, logMap_apply_of_norm_one hy] at this
      have := mul_left_cancel₀ ?_ this
      · refine Real.log_injOn_pos ?_ ?_ this
        all_goals
        · exact lt_iff_le_and_ne.mpr ⟨normAtPlace_nonneg _ _,
            (mixedEmbedding.norm_ne_zero_iff.mp (by simp [hx, hy]) w).symm⟩
      · refine ne_of_gt mult_pos
    refine ⟨x * y⁻¹, ?_, ?_⟩
    · sorry
    · ext
      · simp_rw [Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply]
        rw [inv_mul_cancel_right₀]
        sorry
      · simp_rw [Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply]
        rw [inv_mul_cancel_right₀]
        sorry
  · rintro ⟨ξ, hξ, rfl⟩
    rw [logMap_mul, logMap_of_mem_Xi hξ, zero_add]
    · simp [norm_one_of_mem_Xi hξ]
    · simp [hy]

def gen_pow (e : Fin (rank K) → ℝ) : E K := by
  sorry

variable (K) in
theorem normEqOne_eq :
    normEqOne K = Set.range (fun ξv : (Ξ K) × ((Fin (rank K) → Set.Ico (0 : ℝ) 1)) ↦
      (ξv.1 : E K) * gen_pow (fun i ↦ ξv.2 i)) := by
  sorry


#exit


open Classical in
example : volume (frontier (normLessThanOne K)) = 0 := by
  set F := frontier (normLessThanOne K) with F_def
  let A : ℕ → (Set (E K)) := fun n ↦ (1 - (n + 2 : ℝ)⁻¹) • F
  have hn₀ : ∀ n : ℕ, 0 < 1 - (n + 2 : ℝ)⁻¹ := by
    intro n
    rw [sub_pos, inv_lt_one_iff]
    exact Or.inr (by linarith)
  have hn₁ : ∀ n : ℕ, 1 - (n + 2 : ℝ)⁻¹ ≤ 1 := by
    intro n
    refine (sub_le_self_iff _).mpr (by positivity)
  have h : ∀ x ∈ F, mixedEmbedding.norm x = 1 := by
    rw [F_def]
    intro x hx
    unfold normLessThanOne at hx

    have := Continuous.frontier_preimage_subset (X := fundamentalCone K) (f := Subtype.val) sorry
      (t := {x | mixedEmbedding.norm x ≤ 1})
    dsimp at this
    have := Continuous.frontier_preimage_subset (X := {x : E K | mixedEmbedding.norm x ≤ 1})
      (f := Subtype.val) sorry (t := fundamentalCone K)
    dsimp at this
    have := Continuous.frontier_preimage_subset (X := {x : E K | mixedEmbedding.norm x ≤ 1})
      (f := Subtype.val) sorry (t := fundamentalCone K)
    dsimp at this
    have := Continuous.frontier_preimage_subset (X := E K)
      (f := fun x ↦ mixedEmbedding.norm (x : E K)) sorry
      (t := Set.Icc 0 1)

    sorry
  sorry


open Classical in
theorem volume_normEqOne :
    volume (normEqOne K) = 0 := by
  -- The sets `A n` are all subsets of `normLessThanOne` and their volume is some multiple
  -- of the volume of `normEqOne`. Since the corresponding series diverge if the volume
  -- of `normEqOne` is non-zero and `normLessThanOne` has finite volume since it is bounded,
  -- we get the result by contradiction.
  let A : ℕ → (Set (E K)) := fun n ↦ (1 - (n + 2 : ℝ)⁻¹) • normEqOne K
  have hn₀ : ∀ n : ℕ, 0 < 1 - (n + 2 : ℝ)⁻¹ := by
    intro n
    rw [sub_pos, inv_lt_one_iff]
    exact Or.inr (by linarith)
  have hn₁ : ∀ n : ℕ, 1 - (n + 2 : ℝ)⁻¹ ≤ 1 := by
    intro n
    refine (sub_le_self_iff _).mpr (by positivity)
  have hA₁ : ∀ n : ℕ, A n ⊆ normLessThanOne K := fun n ↦ smul_normEqOne_subset _ (hn₀ n) (hn₁ n)
  have hA₂ : ∀ n : ℕ, volume (A n) =
      ((1 - (n + 2 : ENNReal)⁻¹) ^ finrank ℚ K) * volume (normEqOne K) := fun n ↦ by
    rw [Measure.addHaar_smul, mixedEmbedding.finrank, abs_pow, ENNReal.ofReal_pow (abs_nonneg _),
      abs_eq_self.mpr (hn₀ n).le, ENNReal.ofReal_sub, ENNReal.ofReal_inv_of_pos,
      ENNReal.ofReal_add,
      ENNReal.ofReal_one, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    any_goals positivity
  have hA₃ : ∀ n, NullMeasurableSet (A n) := fun n ↦
    ((measurableSet_normEqOne K).const_smul₀  _).nullMeasurableSet
  have hA₄ : Pairwise (AEDisjoint volume on A) := fun n m hnm ↦ by
    suffices (1 - (n + 2 : ℝ)⁻¹) ^ finrank ℚ K ≠ (1 - (m + 2 : ℝ)⁻¹) ^ finrank ℚ K by
      refine Disjoint.aedisjoint ?_
      dsimp [A]
      rw [smul_normEqOne _ (hn₀ n), smul_normEqOne _ (hn₀ m)]
      refine Set.disjoint_iff_forall_ne.mpr fun _ hx _ hy hxy ↦ ?_
      rw [← hx.2, ← hy.2, ← hxy] at this
      exact this rfl
    rwa [ne_eq, ← Real.rpow_natCast, ← Real.rpow_natCast, Real.rpow_left_inj (hn₀ n).le (hn₀ m).le
      (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)), sub_right_inj, inv_eq_iff_eq_inv, inv_inv,
      add_left_inj, Nat.cast_inj]
  have hA₅ : volume (⋃ i, A i) ≤ volume (normLessThanOne K) := measure_mono (Set.iUnion_subset hA₁)
  have h : volume (normLessThanOne K) < ⊤ := (isBounded_normLessThanOne K).measure_lt_top
  contrapose! h
  refine (le_trans ?_ (tsum_meas_le_meas_iUnion_of_disjoint₀ volume hA₃ hA₄)).trans hA₅
  simp_rw [hA₂, top_le_iff, ENNReal.tsum_mul_right]
  refine ENNReal.mul_eq_top.mpr (Or.inr ⟨?_, h⟩)
  suffices Tendsto (fun n : ℕ ↦ (1 - (n + 2 : ENNReal)⁻¹) ^ finrank ℚ K) atTop (nhds 1) by
    by_contra! h
    exact zero_ne_one <| tendsto_nhds_unique (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h) this
  rw [show nhds (1 : ENNReal) = nhds ((1 - 0) ^ finrank ℚ K) by norm_num]
  refine ENNReal.Tendsto.pow <|
    ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp_rw [show ∀ n : ℕ, (n : ENNReal) + 2 = (n + 2 : ℕ) by exact fun _ ↦ by norm_cast]
  rw [Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ (n : ENNReal)⁻¹)]
  exact ENNReal.tendsto_inv_nat_nhds_zero

theorem frontier_normLessThanOne' :
    frontier (normLessThanOne K) ⊆ frontier X ∪ normEqOne K := by

  have := Continuous.frontier_preimage_subset (X := fundamentalCone K) (f := Subtype.val) sorry
    (t := {x | mixedEmbedding.norm x ≤ 1})
  simp at this

  have t₀ := frontier_le_subset_eq (β := fundamentalCone K) (α := ℝ)
    (f := fun x ↦ mixedEmbedding.norm (x : E K))
    (g := fun _ ↦ 1) sorry sorry
  simp at t₀

  have t₁ : frontier {x : fundamentalCone K | mixedEmbedding.norm (x : E K) ≤ 1} =
    {x : fundamentalCone K | mixedEmbedding.norm (x : E K) = 1} := sorry



  simp at this
  rw [t₁] at this






#exit

theorem frontier_normLessThanOne :
    frontier (normLessThanOne K) = normEqOne K := by
  have := frontier_le_eq_eq (β := fundamentalCone K) (α := ℝ)
    (f := fun x ↦ mixedEmbedding.norm (x : E K))
    (g := fun _ ↦ 1) ?_ ?_ ?_
  · rw [normLessThanOne, normEqOne]
    have := congr_arg (fun s ↦ Subtype.val '' s) this
    simp at this
    convert this
    · ext x
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      refine ⟨?_, ?_⟩
      · intro hx
        refine ⟨?_, ?_⟩
        ·
          sorry
        ·
          sorry
      ·
        sorry
    · sorry
  · refine Continuous.comp' ?_ ?_
    · exact mixedEmbedding.continuous_norm K
    · exact continuous_subtype_val
  · exact continuous_const
  · rintro ⟨x, hx⟩ hx'
    simp at hx'
    simp
    refine frequently_iff_seq_forall.mpr ?_
    refine ⟨?_, ?_, ?_⟩
    · intro n
      refine ⟨?_, ?_⟩
      exact (1 + 1 / (n + 1 : ℝ)) • x
      refine smul_mem_of_mem hx ?_
      positivity
    · rw [show nhds (⟨x, hx⟩ : fundamentalCone K)= nhds ⟨(1 + 0 : ℝ) • x, by simp [hx]⟩ by norm_num]
      refine tendsto_subtype_rng.mpr ?_
      dsimp only
      refine Tendsto.smul_const ?_ _
      refine Tendsto.add ?_ ?_
      · exact tendsto_const_nhds
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · intro n
      rw [mixedEmbedding.norm_smul, ← hx', mul_one]
      refine one_lt_pow ?_ ?_
      · rw [lt_abs]
        left
        rw [lt_add_iff_pos_right]
        positivity
      · refine ne_of_gt ?_
        exact finrank_pos







end normLessOne

variable (K) in
/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (E K) :=
  fundamentalCone K ∩ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoint K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨hx.2.choose_spec.1.choose, ?_, fun _ h ↦ ?_⟩
  · convert hx.2.choose_spec.2
    exact hx.2.choose_spec.1.choose_spec
  · rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h]
    convert hx.2.choose_spec.2.symm
    exact hx.2.choose_spec.1.choose_spec

theorem integralPoint_ne_zero (a : integralPoint K) :
    (a : E K) ≠ 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

/-- For `a : fundamentalCone K`, the unique non-zero algebraic integer which image by
`mixedEmbedding` is equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K)⁰ :=
  ⟨a.prop.2.choose_spec.1.choose, by
    simp_rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, RingOfIntegers.ext_iff,
      a.prop.2.choose_spec.1.choose_spec, ← (mixedEmbedding_injective K).eq_iff, map_zero,
      a.prop.2.choose_spec.2, integralPoint_ne_zero a, not_false_eq_true]⟩

@[simp]
theorem mixedEmbedding_preimageOfIntegralPoint (a : integralPoint K) :
    mixedEmbedding K (preimageOfIntegralPoint a : 𝓞 K) = (a : E K) := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← a.prop.2.choose_spec.2, preimageOfIntegralPoint,
    a.prop.2.choose_spec.1.choose_spec]

theorem preimageOfIntegralPoint_mixedEmbedding {x : (𝓞 K)⁰}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K) :
    preimageOfIntegralPoint (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfIntegralPoint]

theorem exists_unitSMul_mem_integralPoint {x : E K} (hx : x ≠ 0)
    (hx' : x ∈ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoint K := by
  replace hx : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unitSMul_mem hx
  obtain ⟨_, ⟨⟨x, rfl⟩, ⟨_, rfl⟩⟩⟩ := hx'
  exact ⟨u, hu, (u * x : K), ⟨u * x, rfl⟩, by simp_rw [unitSMul_smul, ← map_mul]⟩

theorem torsion_unitSMul_mem_integralPoint {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoint K) :
    ζ • x ∈ integralPoint K := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact ⟨ζ * a, rfl⟩
  · rw [unitSMul_smul, map_mul]

variable (K) in
/-- The map that sends an element of `a : fundamentalCone K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is equal to the group
of roots of unity, we get the equivalence `integralPointQuotEquivAssociates`. -/
def integralPointToAssociates (a : integralPoint K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfIntegralPoint a⟧

@[simp]
theorem integralPointToAssociates_apply (a : integralPoint K) :
    (integralPointToAssociates K a) = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
theorem integralPointToAssociates_surjective :
    Function.Surjective (integralPointToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K := by
    refine exists_unitSMul_mem_integralPoint ?_  ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
    rw [map_ne_zero, RingOfIntegers.coe_ne_zero_iff]
    exact nonZeroDivisors.coe_ne_zero _
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfIntegralPoint,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

@[simps]
instance integralPoint_torsionSMul: SMul (torsion K) (integralPoint K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integralPoint hζ hx⟩

instance : MulAction (torsion K) (integralPoint K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integralPoint_torsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integralPoint_torsionSMul_smul_coe, Submonoid.coe_mul, mul_smul]

theorem integralPointToAssociates_eq_iff (a b : integralPoint K) :
    integralPointToAssociates K a = integralPointToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  simp_rw [integralPointToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfIntegralPoint, integralPoint_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ?_⟩
  · refine ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simp [hu]⟩
    exact (unitSMul_mem_iff_mem_torsion a.prop.1 _).mp (by simp [hu, b.prop.1])
  · exact ⟨unitsNonZeroDivisorsEquiv.symm ζ, by simpa using h⟩

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and
`Associates (𝓞 K)⁰`. -/
def integralPointQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃ Associates (𝓞 K)⁰ := by
  refine Equiv.ofBijective
    (Quotient.lift (integralPointToAssociates K)
      fun _ _ h ↦ ((integralPointToAssociates_eq_iff _ _).mpr h).symm)
    ⟨by
      convert Setoid.ker_lift_injective (integralPointToAssociates K)
      all_goals
      · ext a b
        rw [Setoid.ker_def, eq_comm, integralPointToAssociates_eq_iff b a,
          MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
      (Quot.surjective_lift _).mpr (integralPointToAssociates_surjective K)⟩

@[simp]
theorem integralPointQuotEquivAssociates_apply (a : integralPoint K) :
    integralPointQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfIntegralPoint a⟧ := rfl

theorem integralPoint_torsionSMul_stabilizer {a : integralPoint K} :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfIntegralPoint, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
def integralPointEquiv :
    integralPoint K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integralPoint_torsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ ↦ (integralPointQuotEquivAssociates K).trans
        (associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
theorem integralPointEquiv_apply_fst (a : integralPoint K) :
    ((integralPointEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl

/-- The `mixedEmbedding.norm` of `a : integralPoint K` as a natural integer, see `intNorm_coe` . -/
def intNorm (a : integralPoint K) : ℕ := (Algebra.norm ℤ (preimageOfIntegralPoint a : 𝓞 K)).natAbs

@[simp]
theorem intNorm_coe (a : integralPoint K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : E K) := by
  rw [intNorm, Int.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, mixedEmbedding_preimageOfIntegralPoint]

/-- The norm `intNorm` defined on `fundamentalCone.integralPoint K` lifts to a function
on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℕ :=
  Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ by
    rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integralPoint_torsionSMul_smul_coe,
      norm_unitSMul]

@[simp]
theorem quotIntNorm_apply (a : integralPoint K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
def integralPointEquivNorm (n : ℕ) :
    {a : integralPoint K // intNorm a = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc {a // intNorm a = n}
      ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      (Equiv.subtypeEquiv (integralPointEquiv K) fun _ ↦ by simp [intNorm, absNorm_span_singleton])
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K :=
      Equiv.prodSubtypeFstEquivSubtypeProd (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} ↦
        absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1) (fun I ↦ absNorm I.1 = n))

@[simp]
theorem integralPointEquivNorm_apply_fst {n : ℕ} {a : integralPoint K} (ha : intNorm a = n) :
    ((integralPointEquivNorm K n ⟨a, ha⟩).1 : Ideal (𝓞 K)) =
      span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl

variable (K)

/-- For `n` positive, the number of `fundamentalCone.integralPoint K` of
norm `n` is equal to the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K`. -/
theorem card_isPrincipal_norm_eq (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a = n} := by
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  exact Nat.card_congr (integralPointEquivNorm K n).symm

theorem card_isPrincipal_norm_le (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a ≤ n} := by
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic n) _
      (fun I ↦ ⟨absNorm (I.1 : Ideal (𝓞 K)), Finset.mem_Iic.mpr I.1.2.2⟩)
      (fun a ↦ ⟨intNorm a.1, Finset.mem_Iic.mpr a.2⟩) fun ⟨i, hi⟩ ↦ ?_
  simp_rw [Subtype.mk.injEq]
  calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 ≤ n} // absNorm I.1.1 = i}
          × torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 ≤ n) ∧ absNorm I.1 = i}
          × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
      (p := fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1 ∧ absNorm I.1 ≤ n)
      (q := fun I ↦ absNorm I.1 = i))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i ∧ absNorm I.1 ≤ n}
          × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by aesop)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i} × torsion K :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by
      rw [and_iff_left_of_imp (a := absNorm _ = _) fun h ↦ Finset.mem_Iic.mp (h ▸ hi)])
    _ ≃ {a : integralPoint K // intNorm a = i} := (integralPointEquivNorm K i).symm
    _ ≃ {a : {a : integralPoint K // intNorm a ≤ n} // intNorm a.1 = i} :=
      (Equiv.subtypeSubtypeEquivSubtype fun h ↦ Finset.mem_Iic.mp (h ▸ hi)).symm

end fundamentalCone

end
