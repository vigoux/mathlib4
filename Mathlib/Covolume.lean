import Mathlib.UnitBox
-- import Mathlib.FundamentalCone
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

section OrthonormalBasis



end OrthonormalBasis

noncomputable section

open Submodule Fintype Bornology Filter Topology MeasureTheory MeasureTheory.Measure BoxIntegral

open scoped Pointwise

section General

variable {E ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (c : ℝ) (s : Set E)

theorem toto2 (hc : c ≠ 0) : Nat.card (s ∩ c⁻¹ • span ℤ (Set.range b) : Set E) =
    CountingFunction c (b.equivFun '' s) := by
  refine Nat.card_congr (b.equivFun.toEquiv.subtypeEquiv fun x ↦ ?_)
  simp_rw [Set.mem_inter_iff, LinearEquiv.coe_toEquiv, Basis.equivFun_apply, Set.mem_image,
    DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, and_congr_right_iff,
    Set.mem_inv_smul_set_iff₀ hc, ← Finsupp.coe_smul, ← LinearEquiv.map_smul, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]

variable [MeasurableSpace E] [BorelSpace E]

theorem main2 (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range b) : Set E) : ℝ) / n ^ card ι)
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

end General

section Pi

variable {ι : Type*} [Fintype ι] (b₀ : Basis ι ℝ (ι → ℝ)) (s₀ : Set (ι → ℝ))
  (hs₀₁ : Bornology.IsBounded s₀) (hs₀₂ : MeasurableSet s₀)

theorem main3 :
    Tendsto (fun n : ℕ ↦
      (Nat.card (s₀ ∩ (n : ℝ)⁻¹ • span ℤ (Set.range b₀) : Set (ι → ℝ)) : ℝ) / n ^ card ι)
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

end Pi

section Cone

open Fintype MeasureTheory

variable {E ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable [MeasurableSpace E] [BorelSpace E]

variable (X : Set E) (hX : ∀ ⦃x : E⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})

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

theorem cone₁ [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ span ℤ (Set.range b) : Set E) / (c : ℝ))
        atTop (𝓝 (volume (b.equivFun '' {x ∈ X | F x ≤ 1})).toReal) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  have t0 := main (b.equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ ?_
  have t1 : Tendsto (fun x : ℝ ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop := ?_
  have := Tendsto.comp t0 t1
  refine Tendsto.congr' ?_ this
  filter_upwards [eventually_gt_atTop 0] with c hc
  · rw [Function.comp_apply, ← toto2, ← tool _ _ hX, ← Real.rpow_nat_cast, Real.rpow_inv_rpow]
    · exact le_of_lt hc -- 0 ≤ c
    · rw [Nat.cast_ne_zero]
      exact card_ne_zero -- card ι ≠ 0
    · exact hF₁
    · exact Real.rpow_pos_of_pos hc _ -- 0 < c ^ (card ι)⁻¹
    · exact ne_of_gt (Real.rpow_pos_of_pos hc _) -- c ^ (card ι)⁻¹ ≠ 0
  · refine tendsto_rpow_atTop ?_
    rw [inv_pos, Nat.cast_pos]
    exact card_pos
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hF₂ ⊢
    have := Bornology.IsVonNBounded.image (E := E) (F := ι → ℝ) (σ := RingHom.id ℝ) hF₂
    erw [← LinearMap.coe_toContinuousLinearMap']
    exact this _
  · exact b.equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hF₃
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

end Cone

section InnerProductSpace

open FiniteDimensional Zlattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable  (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]

variable {s : Set E} (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)

theorem volume_eq_volume_div_covolume {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    volume ((b.ofZlatticeBasis ℝ L).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  classical
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [card_fin, finrank_eq_card_basis (b.ofZlatticeBasis ℝ)])
  have h₁ : MeasurableSet ((b.ofZlatticeBasis ℝ L).equivFun '' s) :=
    (b.ofZlatticeBasis ℝ L).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂
  have h₂ : ((stdOrthonormalBasis ℝ E).toBasis.reindex e).det (Subtype.val ∘ b) ≠ 0 := by
    rw [show (Subtype.val ∘ b) = (b.ofZlatticeBasis ℝ) by
      ext; exact (b.ofZlatticeBasis_apply ℝ L _).symm]
    exact isUnit_iff_ne_zero.mp (Basis.isUnit_det _ _)
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv _).measure_preimage h₁]
  rw [← ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr.measure_preimage
    ((MeasurableEquiv.measurableSet_preimage _).mpr h₁)]
  simp_rw [EuclideanSpace.coe_measurableEquiv, ← WithLp.linearEquiv_apply 2 ℝ,
    ← LinearIsometryEquiv.coe_toLinearEquiv, ← LinearEquiv.image_symm_eq_preimage,
    ← Set.image_comp, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, LinearEquiv.comp_coe]
  erw [LinearEquiv.image_eq_preimage]
  rw [addHaar_preimage_linearEquiv, mul_comm, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos
    (covolume_pos L volume), covolume_eq_det_mul_measure L volume b
    ((stdOrthonormalBasis ℝ E).reindex e).toBasis, OrthonormalBasis.reindex_toBasis,
    Zspan.fundamentalDomain_reindex, measure_congr (Zspan.fundamentalDomain_ae_parallelepiped _
    volume), OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped,
    ENNReal.one_toReal, mul_one, ← abs_inv]
  congr
  rw [← mul_eq_one_iff_eq_inv₀ (by convert h₂), ← Basis.det_comp]
  convert Basis.det_self _
  · ext
    simp_rw [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.trans_apply, Basis.equivFun_apply, ← b.ofZlatticeBasis_apply ℝ, Basis.repr_self,
      Finsupp.single_eq_pi_single, WithLp.linearEquiv_symm_apply, WithLp.equiv_symm_single _ (1:ℝ),
      LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.coe_toLinearEquiv,
      OrthonormalBasis.repr_symm_single, OrthonormalBasis.coe_reindex, Basis.coe_reindex,
      OrthonormalBasis.coe_toBasis]

-- These below are not wanted as they are direct consequences of the previous result

example :  Tendsto (fun n : ℕ ↦ ( Nat.card (s ∩ (n⁻¹ : ℝ) • L : Set E) : ℝ) / n ^ finrank ℝ E)
     atTop (𝓝 ((volume s).toReal / Zlattice.covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert main2 (b.ofZlatticeBasis ℝ) s hs₁ hs₂
  · simp_rw [← b.ofZlatticeBasis_span ℝ]
    rfl
  · rw [← finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ L]
  · rw [volume_eq_volume_div_covolume L hs₂, ENNReal.toReal_div, ENNReal.toReal_ofReal]
    exact le_of_lt (covolume_pos L)

variable (X : Set E) (hX : ∀ ⦃x : E⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ finrank ℝ E * (F x))
  (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})

theorem cone₂ [Nontrivial E] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / c)
        atTop (𝓝 ((volume {x ∈ X | F x ≤ 1}).toReal / Zlattice.covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert (cone₁ (b.ofZlatticeBasis ℝ) X hX F ?_ hF₂ hF₃)
  · change (L : Set E) = (span ℤ (Set.range (b.ofZlatticeBasis ℝ))).toAddSubgroup
    exact_mod_cast (b.ofZlatticeBasis_span ℝ).symm
  · rw [volume_eq_volume_div_covolume L hF₃, ENNReal.toReal_div, ENNReal.toReal_ofReal]
    exact le_of_lt (covolume_pos L)
  · rwa [← finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ L]

end InnerProductSpace
