import Mathlib.Logic.Equiv.Defs
-- import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
-- import Mathlib.Algebra.Module.Zlattice.Covolume

variable {α β : Type*} (p : α → Prop)

def prodSubtypeEquivSubtypeProd : {s : α × β // p s.1} ≃ {a // p a} × β where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

#exit

  refine Equiv.trans (Equiv.subtypeProdEquivSigmaSubtype fun a ↦ fun b ↦ p a) ?_
  exact?
  refine Equiv.trans ?_ (Equiv.sigmaEquivProd _ _)

  --refine Equiv.trans ?_ (Equiv.subtypeSigmaEquiv _ (fun a ↦ p a))
  -- refine Equiv.trans (Equiv.subtypeSigmaEquiv _ (fun a ↦ p a)) ?_

  sorry

end logic

#exit

section Topo

theorem closure_lt_eq_le {α β : Type*} [TopologicalSpace α] [PartialOrder α] [OrderClosedTopology α]
    [TopologicalSpace β] {f : β → α}  {g : β → α} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    closure {b | f b < g b} = {b | f b ≤ g b} := by
  refine le_antisymm (closure_lt_subset_le hf hg) fun x hx ↦ ?_
  obtain (hx₁| hx₂) := le_iff_eq_or_lt.mp hx
  · exact mem_closure_iff_frequently.mpr (h hx₁)
  · exact subset_closure hx₂

theorem frontier_le_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, g x = f x → ∃ᶠ y in nhds x, g y < f y) :
    frontier {b | f b ≤ g b} = {b | f b = g b} := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  ext x
  rw [show {x | f x ≤ g x}ᶜ = {x | g x < f x} by ext; simp, closure_lt_eq_le hg hf h]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_antisymm_iff]

theorem frontier_lt_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    frontier {b | f b < g b} = {b | f b = g b} := by
  simpa only [eq_comm, ← not_lt, ← Set.compl_setOf, frontier_compl] using frontier_le_eq_eq hg hf h

end Topo

section Module

variable {ι : Type*} [IsEmpty ι] (M : Type*) [AddCommMonoid M] {R : Type*} [Semiring R] [Module R M]
variable (b : Basis ι R M)

example : Subsingleton M := by
  have : Fintype ι := Fintype.ofIsEmpty
  exact subsingleton_of_forall_eq 0 fun y ↦ by rw [← b.sum_repr y, Fintype.sum_empty]

end Module

section PiLp

open Bornology Filter

variable {ι : Type*} [Fintype ι] (R M : Type*) [NormedDivisionRing R] [SeminormedAddCommGroup M]
  [Module R M] (b : Basis ι R M) (s : Set M)

variable [BoundedSMul R M]

example [IsEmpty ι] : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun y ↦ ?_
  rw [← b.sum_repr y, Fintype.sum_empty]

example (h : ∀ i, IsBounded ((fun x ↦ b.repr x i) '' s)) :
    IsBounded s := by
  by_cases hι : IsEmpty ι
  · have : Subsingleton M := by
      sorry
    have : IsBounded (⊤ : Set M) := by exact IsBounded.all ⊤
    refine IsBounded.subset this le_top
  · obtain ⟨C, hC⟩ : ∃ C, ∀ i, ‖b i‖ ≤ C := by
      refine ⟨?_, ?_⟩
      refine Finset.univ.sup' ?_ (fun i ↦ ‖b i‖)
      rw [Finset.univ_nonempty_iff]
      exact not_isEmpty_iff.mp hι
      exact fun i ↦ Finset.le_sup' (fun i ↦ ‖b i‖) (Finset.mem_univ i)
    obtain ⟨D, hD₁, hD₂⟩ : ∃ D ≥ 0, ∀ i, ∀ x ∈ s, ‖b.repr x i‖ ≤ D := by
      simp_rw [Metric.isBounded_iff_subset_closedBall (0:R)] at h
      let D := Finset.univ.sup' ?_ fun i ↦ (h i).choose
      refine ⟨D, ?_, ?_⟩
      sorry
      intro i x hx
      specialize h i
      have := h.choose_spec
      have : ‖b.repr x i‖ ≤ h.choose := by
        sorry
      sorry
      sorry
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨?_, ?_⟩
    · exact (Fintype.card ι) • (D * C)
    · intro x hx
      rw [mem_closedBall_zero_iff, ← b.sum_repr x]
      refine le_trans (norm_sum_le _ _) ?_
      simp_rw [norm_smul]
      rw [Fintype.card, ← Finset.sum_const]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      gcongr
      · exact hD₂ i x hx
      · exact hC i

variable (p : ENNReal) (𝕜 : Type*) {ι : Type*} (β : ι → Type*) [Fact (1 ≤ p)] [Fintype ι]
  [NormedField 𝕜] [(i : ι) → SeminormedAddCommGroup (β i)]  [(i : ι) → NormedSpace 𝕜 (β i)]

example (s : Set (PiLp p β)) :
    IsBounded s ↔ ∀ i, IsBounded ((fun x ↦ ‖x i‖) '' s) := by
  refine ⟨?_, ?_⟩
  · rw [Metric.isBounded_iff_subset_ball 0]
    intro h i
    rw [Metric.isBounded_iff_subset_ball 0]

    sorry
  ·
    sorry


end PiLp

open Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

namespace NumberField.mixedEmbedding.euclideanSpace

open NumberField NumberField.InfinitePlace MeasureTheory BigOperators Submodule

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

/-- Docs. -/
local instance : Ring (EuclideanSpace ℝ { w : InfinitePlace K // IsReal w }) := Pi.ring

/-- Docs. -/
local instance : Ring (EuclideanSpace ℂ { w : InfinitePlace K // IsComplex w }) := Pi.ring

instance : Ring (E₂ K) := Prod.instRing

instance : MeasurableSpace (E₂ K) := borel _

instance : BorelSpace (E₂ K)  :=  ⟨rfl⟩

instance : T2Space (E₂ K) := Prod.t2Space

protected theorem norm_apply (x : E₂ K) :
    ‖x‖ = Real.sqrt (∑ w, ‖x.1 w‖ ^ 2 + ∑ w, ‖x.2 w‖ ^ 2) := by
  rw [WithLp.prod_norm_eq_add (by exact Nat.ofNat_pos), EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq, ENNReal.toReal_ofNat, Real.rpow_two, Real.sq_sqrt (by positivity),
    Real.rpow_two, Real.sq_sqrt (by positivity), Real.sqrt_eq_rpow]

-- protected theorem inner_apply (x y : E₂ K) :
--     ⟪x, y⟫_ℝ = ∑ w, (x.1 w) * (y.1 w) +
--       ∑ w, ((x.2 w).re * (y.2 w).re + (x.2 w).im * (y.2 w).im) := by
--   simp_rw [WithLp.prod_inner_apply, EuclideanSpace.inner_eq_star_dotProduct, real_inner_eq_re_inner,
--     EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct, Pi.star_apply, star_trivial,
--     RCLike.star_def, map_sum, RCLike.mul_re, RCLike.conj_re, RCLike.re_to_complex,
--     RCLike.conj_im, WithLp.equiv_pi_apply, neg_mul, sub_neg_eq_add, RCLike.im_to_complex]

/-- Docs. -/
protected def linearEquiv : (E₂ K) ≃ₗ[ℝ] (E K) := WithLp.linearEquiv _ _ _

/-- Docs. -/
protected def continuousLinearEquiv : (E₂ K) ≃L[ℝ] (E K) :=
  (euclideanSpace.linearEquiv K).toContinuousLinearEquiv

/-- Docs. -/
protected def homeomorph : (E₂ K) ≃ₜ (E K) :=
  (euclideanSpace.continuousLinearEquiv K).toHomeomorph

/-- Docs. -/
-- protected def addEquiv : (E₂ K) ≃+ (E K) := (euclideanSpace.linearEquiv K).toAddEquiv

protected theorem coe_homeomorph :
  ⇑(euclideanSpace.linearEquiv K) = ⇑(euclideanSpace.homeomorph K) := rfl

protected theorem coe_continuousLinearEquiv :
  ⇑(euclideanSpace.linearEquiv K) = ⇑(euclideanSpace.continuousLinearEquiv K) := rfl

instance : Nontrivial (E₂ K) := (euclideanSpace.linearEquiv K).toEquiv.nontrivial

/-- Docs. -/
protected def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (E₂ K) := sorry

theorem stdOrthonormalBasis_equiv :
    (euclideanSpace.stdOrthonormalBasis K).toBasis.map (euclideanSpace.linearEquiv K) =
      mixedEmbedding.stdBasis K := sorry

theorem measurePreserving_euclideanLinearEquiv :
    MeasurePreserving (euclideanSpace.linearEquiv K) := by
  let e := (euclideanSpace.homeomorph K).toMeasurableEquiv
  convert e.measurable.measurePreserving volume
  erw [← (OrthonormalBasis.addHaar_eq_volume (euclideanSpace.stdOrthonormalBasis K)),
    Homeomorph.toMeasurableEquiv_coe, Basis.map_addHaar _ (euclideanSpace.continuousLinearEquiv K),
    stdOrthonormalBasis_equiv, eq_comm, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
    ← measure_congr (Zspan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
    volume_fundamentalDomain_stdBasis K]

end NumberField.mixedEmbedding.euclideanSpace

open Filter NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Topology MeasureTheory
  NumberField.Units NumberField.mixedEmbedding.fundamentalCone Submodule Bornology
  NumberField.mixedEmbedding.euclideanSpace FiniteDimensional NumberField.Units.dirichletUnitTheorem

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- Docs. -/
def Λ : AddSubgroup (E₂ K) :=
    (span ℤ (Set.range ((latticeBasis K).map (euclideanSpace.linearEquiv K).symm))).toAddSubgroup

instance : DiscreteTopology (Λ K) := Zspan.instDiscreteTopology _

instance : IsZlattice ℝ (Λ K) where
  span_top := by
    simp_rw [Λ, coe_toAddSubgroup, ← Zspan.map, map_coe, LinearEquiv.restrictScalars_apply,
      ← Submodule.map_span, Zspan.span_top, Submodule.map_top, LinearEquivClass.range]

/-- Docs. -/
abbrev X : Set (E₂ K) := (euclideanSpace.linearEquiv K)⁻¹' (fundamentalCone K)

/-- Docs. -/
abbrev X₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.linearEquiv K x) ≤ 1}

/-- Docs. -/
abbrev F₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.linearEquiv K x) = 1}

variable {K}

theorem aux00 {x : E₂ K} (hx : x ∈ X K) (hx' : x ≠ 0) :
    0 < mixedEmbedding.norm (euclideanSpace.linearEquiv K x) := by
  rw [X, fundamentalCone, Set.mem_preimage] at hx
  have := hx.resolve_right ?_
  refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
  · exact mixedEmbedding.norm_nonneg _
  · exact Ne.symm this.2
  rw [Set.mem_singleton_iff, AddEquivClass.map_eq_zero_iff]
  exact hx'

theorem aux0 {x : E₂ K} (hx : x ∈ X₁ K) (hx' : x ≠ 0) :
    ∃ c : ℝ, 1 ≤ c ∧ c • x ∈ F₁ K := by
  refine ⟨((mixedEmbedding.norm (euclideanSpace.linearEquiv K x)) ^ (-(finrank ℚ K : ℝ)⁻¹)), ?_, ?_⟩
  · refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
    · exact aux00 hx.1 hx'
    · exact hx.2
    · simp
  · refine ⟨?_, ?_⟩
    · rw [X, Set.mem_preimage, _root_.map_smul]
      exact smul_mem_of_mem hx.1 _
    · rw [_root_.map_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr]
      rw [← Real.rpow_natCast, ← Real.rpow_mul, neg_mul, inv_mul_cancel, Real.rpow_neg_one,
        inv_mul_cancel]
      · exact ne_of_gt (aux00 hx.1 hx')
      · rw [Nat.cast_ne_zero]
        exact ne_of_gt finrank_pos
      · exact mixedEmbedding.norm_nonneg _
      · refine Real.rpow_nonneg ?_ _
        exact mixedEmbedding.norm_nonneg _

theorem aux1 (h : IsBounded (F₁ K)) :
    IsBounded (X₁ K) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  obtain ⟨r, hr₁, hr₂⟩ := h.subset_ball_lt 0 0
  refine ⟨r, ?_⟩
  rintro x hx
  by_cases hx' : x = 0
  · rw [hx']
    exact Metric.mem_ball_self hr₁
  · obtain ⟨c, hc₁, hc₂⟩ := aux0 hx hx'
    have := hr₂ hc₂
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_smul, ← lt_div_iff'] at this
    refine lt_of_lt_of_le this ?_
    refine div_le_self ?_ ?_
    exact le_of_lt hr₁
    rw [Real.norm_eq_abs]
    exact le_trans hc₁ (le_abs_self _)
    rw [norm_pos_iff]
    refine ne_of_gt ?_
    exact lt_of_lt_of_le zero_lt_one hc₁

theorem aux11 : frontier (X₁ K) = F₁ K := sorry

theorem logMap_apply_F₁_ofIsReal {x : E₂ K} (hx : x ∈ F₁ K) {w : InfinitePlace K} (hw₁ : w ≠ w₀)
    (hw₂ : IsReal w) :
    logMap (euclideanSpace.linearEquiv K x) ⟨w, hw₁⟩ = Real.log ‖x.1 ⟨w, hw₂⟩‖ := by
  rw [logMap, dif_pos hw₂, hx.2, Real.log_one, zero_mul, sub_zero]
  rfl

theorem logMap_apply_F₁_ofIsComplex {x : E₂ K} (hx : x ∈ F₁ K) {w : InfinitePlace K} (hw₁ : w ≠ w₀)
    (hw₂ : IsComplex w) :
    logMap (euclideanSpace.linearEquiv K x) ⟨w, hw₁⟩ = 2 * Real.log ‖x.2 ⟨w, hw₂⟩‖ := by
  rw [logMap, dif_neg (not_isReal_iff_isComplex.mpr hw₂), hx.2, Real.log_one, zero_mul, sub_zero]
  rfl

theorem aux2 : IsBounded (F₁ K) := by
  rsuffices ⟨C, _, hC⟩ : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ x ∈ (F₁ K),
        (∀ w, w.val ≠ w₀ → C₁ < ‖x.1 w‖ ∧ ‖x.1 w‖ < C₂) ∧
        (∀ w, w.val ≠ w₀ → C₁ < ‖x.2 w‖ ∧ ‖x.2 w‖ < C₂) := by
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
    have := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
    obtain ⟨r, hr₁, hr₂⟩ := this
    refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.exp_pos _, fun x hx₁ ↦ ?_⟩
    have hx₂ : x ≠ 0 := sorry
    have hx₃ : (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := sorry
    have hx₄ :  ∀ w : { w // w ≠ w₀ }, ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r := by
      rw [← pi_norm_lt_iff hr₁, ← mem_ball_zero_iff]
      refine hr₂ ?_
      have := hx₁.1
      rw [X, fundamentalCone, Set.mem_preimage] at this
      exact (this.resolve_right (by simp [hx₂])).1

    refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
      rw [← logMap_apply_F₁_ofIsReal hx₁ hw]
      exact hx₄ ⟨w.val, hw⟩
      sorry
      sorry
    · rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
      refine lt_trans ?_ (div_two_lt_of_pos hr₁)
      rw [← mul_lt_mul_left (zero_lt_two)]
      rw [mul_div_cancel₀ _ (two_ne_zero)]
      rw [show (2:ℝ) = |2| by norm_num, ← abs_mul]
      rw [← logMap_apply_F₁_ofIsComplex hx₁ hw]
      exact hx₄ ⟨w.val, hw⟩
      sorry
      sorry
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨?_, ?_⟩
  · sorry
  · intro x hx
    rw [mem_closedBall_zero_iff, euclideanSpace.norm_apply]
    sorry

variable (K) in
def iso3 : ↑(↑(Λ K) ∩ X K) ≃ integralPoint K :=
  Equiv.subtypeEquiv (euclideanSpace.linearEquiv _).toEquiv fun x ↦ by
  simp only [Λ, coe_toAddSubgroup, Set.inter_comm _ (X K), Set.mem_inter_iff, Set.mem_preimage,
    SetLike.mem_coe, LinearEquiv.coe_toEquiv, integralPoint, Set.mem_image, Set.mem_range,
    exists_exists_eq_and, and_congr_right_iff]
  intro _
  rw [← Zspan.map]
  rw [Submodule.mem_map]
  simp_rw [mem_span_latticeBasis]
  simp only [RingHom.mem_range, RingHom.coe_comp, Function.comp_apply,
    LinearEquiv.restrictScalars_apply, exists_exists_eq_and]
  simp_rw [LinearEquiv.symm_apply_eq]

@[simp]
theorem iso3_apply (x : ↑(↑(Λ K) ∩ X K)) :
    iso3 K x = euclideanSpace.linearEquiv K (x : E₂ K) := rfl

open Asymptotics Submodule Ideal nonZeroDivisors

example :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal I.val ∧ absNorm I.val ≤ n} *
        torsionOrder K : ℝ) / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
    (Tendsto.comp (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_)
      tendsto_natCast_atTop_atTop)
  · filter_upwards with n
    have := card_isPrincipal_norm_le K n
    simp_rw [Function.comp_apply, ← Nat.cast_mul]
    rw [this]
    simp_rw [Set.setOf_inter_eq_sep, ← and_assoc, ← Set.mem_inter_iff]
    congr 2
    refine Nat.card_congr ?_
    refine Equiv.trans (Equiv.Set.sep _ _) ?_
    refine Equiv.subtypeEquiv (iso3 K) ?_
    intro x
    simp_rw [Set.mem_setOf_eq, ← Nat.cast_le (α := ℝ), intNorm_coe]
    have := iso3_apply x
    rw [this]

#exit

example :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) | Submodule.IsPrincipal I ∧ Ideal.absNorm I ∈ Finset.Icc 1 n} *
        torsionOrder K : ℝ) / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
--  refine IsEquivalent.tendsto_nhds ?_
    (Tendsto.comp (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_)
      tendsto_natCast_atTop_atTop)
  · have := card_isPrincipal_norm_le_div_atTop K
    refine IsEquivalent.trans ?_ this.symm
    refine EventuallyEq.isEquivalent ?_
    filter_upwards with _
    simp_rw [Function.comp_apply, Set.setOf_inter_eq_sep, ← and_assoc, ← Set.mem_inter_iff]
    -- have := card_isPrincipal_norm_in_Icc K c
    -- simp_rw [this]
    congr 2
    refine Nat.card_congr ?_
    refine Equiv.trans (Equiv.Set.sep _ _) ?_
    refine Equiv.subtypeEquiv (iso3 K) ?_
    intro x
    simp_rw [Set.mem_setOf_eq, ← Nat.cast_le (α := ℝ), intNorm_coe]
    have := iso3_apply x
    rw [this]
  · intro x r hx hr
    erw [Set.mem_preimage, _root_.map_smul (euclideanSpace.linearEquiv K)]
    refine smul_mem_of_mem ?_ r
    exact hx
  · intro x r hr
    rw [_root_.map_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr hr]
    erw [mixedEmbedding.finrank]
  · -- Not trivial at all
    sorry
  · refine MeasurableSet.inter ?_ ?_
    · rw [X]
      refine measurableSet_preimage (euclideanSpace.homeomorph K).measurable ?_
      sorry
    · refine measurableSet_le (f := fun x ↦ mixedEmbedding.norm (euclideanSpace.linearEquiv K x))
        (g := fun _ ↦ 1) ?_ ?_
      sorry
      exact measurable_const

#lint
