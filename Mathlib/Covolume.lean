import Mathlib.UnitBox
import Mathlib.FundamentalCone
import Mathlib.Algebra.Module.Zlattice.Covolume

noncomputable section

open Submodule Fintype Bornology Filter Topology MeasureTheory MeasureTheory.Measure BoxIntegral

open scoped Pointwise

-- Do not use a basis but a IsZlattice instead
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] -- (b : Basis ι ℝ E)
variable  (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]

variable (c : ℝ) (s : Set E)

abbrev LatticePoints  : Set E := s ∩ c⁻¹ • span ℤ (Set.range b)

def LatticeCountingFunction := Nat.card (LatticePoints b c s)

variable [Fintype ι]

theorem toto2 (hc : c ≠ 0) : LatticeCountingFunction b c s =
    CountingFunction c (b.equivFun '' s) := by
  refine Nat.card_congr (b.equivFun.toEquiv.subtypeEquiv fun x ↦ ?_)
  simp_rw [Set.mem_inter_iff, LinearEquiv.coe_toEquiv, Basis.equivFun_apply, Set.mem_image,
    DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, and_congr_right_iff,
    Set.mem_inv_smul_set_iff₀ hc, ← Finsupp.coe_smul, ← LinearEquiv.map_smul, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]

variable [MeasurableSpace E] [BorelSpace E]

theorem main2 (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (LatticeCountingFunction b n s : ℝ) / n ^ card ι)
      atTop (𝓝 (volume (b.equivFun '' s)).toReal) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  refine Tendsto.congr' ?_ (main' (b.equivFun '' s) ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0]
    intro c hc
    congr
    have := toto2 b c s ?_
    exact this.symm
    rw [Nat.cast_ne_zero]
    refine ne_of_gt hc
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    have := Bornology.IsVonNBounded.image (E := E) (F := ι → ℝ) (σ := RingHom.id ℝ) hs₁
    erw [← LinearMap.coe_toContinuousLinearMap']
    exact this _
  · rw [LinearEquiv.image_eq_preimage]
    have : Continuous b.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    have : Measurable b.equivFun.symm := by
      exact Continuous.measurable this
    exact this hs₂

variable (b₀ : Basis ι ℝ (ι → ℝ)) (s₀ : Set (ι → ℝ)) (hs₀₁ : Bornology.IsBounded s₀)
  (hs₀₂ : MeasurableSet s₀)

theorem main3 :
    Tendsto (fun n : ℕ ↦ (LatticeCountingFunction b₀ n s₀ : ℝ) / n ^ card ι)
      atTop (𝓝 (|(LinearEquiv.det b₀.equivFun : ℝ)| * (volume s₀).toReal)) := by
  convert main2 b₀ s₀ hs₀₁ hs₀₂ using 2
  rw [LinearEquiv.image_eq_preimage]
  rw [← MeasureTheory.Measure.map_apply₀]
  · erw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
    · rw [LinearEquiv.det_coe_symm, inv_inv]
      simp only [LinearEquiv.coe_det, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_mul, abs_nonneg, ENNReal.toReal_ofReal]
    · refine IsUnit.ne_zero ?_
      exact LinearEquiv.isUnit_det' _
  · have : Continuous b₀.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    exact Continuous.aemeasurable this
  · exact MeasurableSet.nullMeasurableSet hs₀₂

variable (X : Set E) (hX : ∀ ⦃x : E⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x | F x ≤ 1}) (hF₃ : MeasurableSet {x | F x ≤ 1})

open Submodule

theorem tool (B : ℝ) (hB : 0 < B) :
    Nat.card ({x ∈ X  | F x ≤ B ^ card ι} ∩ span ℤ (Set.range b) : Set E) =
      Nat.card ({x ∈ X | F x ≤ 1 } ∩ B⁻¹ • (span ℤ (Set.range b)) : Set E) := by
  have hB₂ : 0 ≤ B⁻¹ := inv_nonneg.mpr (le_of_lt hB)
  have hB₃ : B⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hB)
  refine Nat.card_congr <| Equiv.subtypeEquiv (Equiv.smulRight hB₃) (fun a ↦ ?_)
  simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀
    hB₃, SetLike.mem_coe, hF₁ a hB₂, inv_pow, inv_mul_le_iff (pow_pos hB _), mul_one,
    and_congr_left_iff]
  refine fun _ _ ↦ ⟨fun h ↦ hX h hB₂, fun h ↦ ?_⟩
  convert hX h (le_of_lt hB)
  rw [smul_inv_smul₀ (ne_of_gt hB)]

example [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ span ℤ (Set.range b) : Set E) / (c : ℝ))
        atTop (𝓝 (volume (b.equivFun '' {x ∈ X | F x ≤ 1})).toReal) := by
  have t0 := main (b.equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ ?_
  have t1 : Tendsto (fun x : ℝ ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop := ?_
  have := Tendsto.comp t0 t1
  refine Tendsto.congr' ?_ this
  filter_upwards [eventually_gt_atTop 0] with c hc
  · rw [Function.comp_apply, ← toto2, LatticeCountingFunction, LatticePoints, ← tool _ _ hX,
      ← Real.rpow_nat_cast, Real.rpow_inv_rpow]
    · exact le_of_lt hc -- 0 ≤ c
    · rw [Nat.cast_ne_zero]
      exact card_ne_zero -- card ι ≠ 0
    · exact hF₁
    · exact Real.rpow_pos_of_pos hc _ -- 0 < c ^ (card ι)⁻¹
    · exact ne_of_gt (Real.rpow_pos_of_pos hc _) -- c ^ (card ι)⁻¹ ≠ 0
  · refine tendsto_rpow_atTop ?_
    rw [inv_pos, Nat.cast_pos]
    exact card_pos
  · sorry
  · sorry
  · intro c c' h₁ h₂
    have i₁ : 0 ≤ c'⁻¹ * c := by
      refine mul_nonneg ?_ ?_
      refine inv_nonneg.mpr ?_
      exact le_trans (le_of_lt h₁) h₂
      exact le_of_lt h₁
    simp_rw [← image_smul_set]
    refine Set.image_mono ?_
    intro _
    rw [Set.mem_smul_set, Set.mem_smul_set]
    rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨(c'⁻¹ * c) • x, ⟨?_, ?_⟩, ?_⟩
    · refine hX hx₁ ?_
      exact i₁
    · rw [hF₁ x ?_, mul_comm]
      refine mul_le_one hx₂ ?_ ?_
      · refine pow_nonneg i₁ _ --  0 ≤ (c'⁻¹ * c) ^ card ι
      · refine pow_le_one _ ?_ ?_
        exact i₁
        rwa [inv_mul_le_iff', one_mul]
        exact lt_of_lt_of_le h₁ h₂
      · exact i₁
    · rw [← smul_assoc, smul_eq_mul, mul_inv_cancel_left₀]
      refine ne_of_gt ?_
      exact lt_of_lt_of_le h₁ h₂
