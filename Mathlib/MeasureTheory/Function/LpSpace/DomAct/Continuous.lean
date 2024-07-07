import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open scoped ENNReal symmDiff Topology
open MeasureTheory Filter Set

namespace DomMulAct

variable {X : Type*} [TopologicalSpace X]

instance instTopologicalSpace : TopologicalSpace Xᵈᵐᵃ := .induced mk.symm  ‹_›

def mkHomeomorph : X ≃ₜ Xᵈᵐᵃ where
  toEquiv := mk
  continuous_toFun := continuous_induced_rng.2 continuous_id
  continuous_invFun := continuous_induced_dom

@[simp] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : X ≃ₜ Xᵈᵐᵃ) = mk := rfl

end DomMulAct

theorem tendsto_measure_symmDiff_preimage_nhds_zero {α X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {s : Set Y} {μX : Measure X} {μY : Measure Y}
    [μX.InnerRegularCompactLTTop] [μY.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μY]
    (hf : ∀ᶠ a in l, MeasurePreserving (f a) μX μY) (hg : MeasurePreserving g μX μY)
    (hfg : Tendsto f l (𝓝 g)) (hs : MeasurableSet s) (hμs : μY s ≠ ∞) :
    Tendsto (fun a ↦ μX ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  wlog hso : IsOpen s generalizing s ε
  · have H : 0 < ε / 3 := by simp [hε.ne']
    rcases hs.exists_isOpen_symmDiff_lt hμs H.ne' with ⟨U, hUo, hU, hUs⟩
    filter_upwards [hf, this hUo.measurableSet hU.ne _ H hUo] with a hfa ha
    calc
      μX ((f a ⁻¹' s) ∆ (g ⁻¹' s))
        ≤ μX ((f a ⁻¹' s) ∆ (f a ⁻¹' U)) + μX ((f a ⁻¹' U) ∆ (g ⁻¹' U))
          + μX ((g ⁻¹' U) ∆ (g ⁻¹' s)) := by
        refine (measure_symmDiff_le _ (g ⁻¹' U) _).trans ?_
        gcongr
        apply measure_symmDiff_le
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · rw [← preimage_symmDiff, hfa.measure_preimage (hs.symmDiff hUo.measurableSet),
            symmDiff_comm]
          exact hUs.le
        · rw [← preimage_symmDiff, hg.measure_preimage (hUo.measurableSet.symmDiff hs)]
          exact hUs.le
      _ = ε := by simp
  have hμs' : μX (g ⁻¹' s) ≠ ∞ := by rwa [hg.measure_preimage hs]
  obtain ⟨K, hKg, hKco, hKcl, hKμ⟩ :
      ∃ K, MapsTo g K s ∧ IsCompact K ∧ IsClosed K ∧ μX (g ⁻¹' s \ K) < ε / 2 :=
    (hs.preimage hg.measurable).exists_isCompact_isClosed_diff_lt hμs' <| by simp [hε.ne']
  filter_upwards [hf, ContinuousMap.tendsto_nhds_compactOpen.mp hfg K hKco s hso hKg] with a hfa ha
  rw [← ENNReal.add_halves ε]
  refine (measure_symmDiff_le _ K _).trans ?_
  rw [symmDiff_of_ge ha.subset_preimage, symmDiff_of_le hKg.subset_preimage]
  gcongr
  have hK' : μX K ≠ ∞ := ne_top_of_le_ne_top hμs' <| measure_mono hKg.subset_preimage
  rw [measure_diff_le_iff_le_add hKcl.measurableSet ha.subset_preimage hK', hfa.measure_preimage hs,
    ← hg.measure_preimage hs,
    ← measure_diff_le_iff_le_add hKcl.measurableSet hKg.subset_preimage hK']
  exact hKμ.le

variable {M X E : Type*}
  [Monoid M] [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [MulAction M X]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [ContinuousSMul M X]
  [R1Space X] [CompactSpace X]
  [NormedAddCommGroup E] [SecondCountableTopologyEither X E]
  {μ : Measure X} [SMulInvariantMeasure M X μ]
  [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
  {p : ℝ≥0∞} [hp₁ : Fact (1 ≤ p)] [hp : Fact (p ≠ ∞)]

instance DomMulAct.instContinuousSMulLp : ContinuousSMul Mᵈᵐᵃ (Lp E p μ) where
  continuous_smul := by
    suffices Continuous fun x : Lp E p μ × M ↦ DomMulAct.mk x.2 • x.1 by
      exact ((Homeomorph.prodComm _ _).trans <|
        mkHomeomorph.prodCongr (Homeomorph.refl _)).comp_continuous_iff'.1 this
    refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (MeasureTheory.Lp.simpleFunc.denseRange hp.out) ?cont
      fun c ↦ (isometry_smul _ (DomMulAct.mk c)).lipschitz
    rintro _ ⟨f, rfl⟩
    induction f using Lp.simpleFunc.induction (one_pos.trans_le hp₁.out).ne' hp.out with
    | @h_ind c s hs hμs =>
      dsimp [mk_smul_indicatorConstLp]
      refine continuous_indicatorConstLp_set hp.out fun a ↦ ?_
      have := (ContinuousMap.mk _ continuous_smul : C(M × X, X)).curry.continuousAt a
      have := tendsto_measure_symmDiff_preimage_nhds_zero (μX := μ) ?_ ?_ this hs hμs.ne
      exact this
      exact eventually_of_forall fun _ ↦ measurePreserving_smul _ _
      apply measurePreserving_smul
    | h_add hfp hgp _ hf hg =>
      exact hf.add hg
