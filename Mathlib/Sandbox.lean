import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.Algebra.Module.Zlattice.Covolume

section Real

theorem Real.sqrt_le_seft {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x ≤ x := by
  refine sqrt_le_iff.mpr ⟨?_, ?_⟩
  sorry
  refine le_self_pow hx two_ne_zero

end Real

section Topo

open Set

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

-- section Module

-- variable {ι : Type*} [IsEmpty ι] (M : Type*) [AddCommMonoid M] {R : Type*} [Semiring R] [Module R M]
-- variable (b : Basis ι R M)

-- example : Subsingleton M := by
--   have : Fintype ι := Fintype.ofIsEmpty
--   exact subsingleton_of_forall_eq 0 fun y ↦ by rw [← b.sum_repr y, Fintype.sum_empty]

-- end Module

section PiLp

open Bornology Filter BigOperators

variable {ι : Type*} [Fintype ι] {R M : Type*} [NormedDivisionRing R] [SeminormedAddCommGroup M]
  [Module R M] [BoundedSMul R M]

theorem Bornology.isBoundedOfBoundedCoeff (v : ι → M) {s : Set R} (h : IsBounded s) :
    IsBounded (Set.range fun (c : ι → s) ↦ ∑ i, (c i : R) • v i) := by
  generalize Finset.univ (α := ι) = t
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := isBounded_iff_forall_norm_le.mp h
  induction t using Finset.cons_induction_on with
  | h₁ =>
      exact Metric.isBounded_range_iff.mpr ⟨0, by simp⟩
  | @h₂ a _ h_ne h_bd =>
      rw [isBounded_iff_forall_norm_le] at h_bd ⊢
      obtain ⟨C₁, hC₁⟩ := h_bd
      refine ⟨C * ‖v a‖ + C₁, fun x ⟨c, hc⟩ ↦ ?_⟩
      simp_rw [← hc, Finset.sum_cons]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul]
      gcongr
      · exact hC (c a) (c a).prop
      · exact hC₁ _ ⟨c, rfl⟩

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

@[simp]
theorem linearEquiv_apply_ofIsReal (x : E₂ K) {w : InfinitePlace K} (hw : IsReal w) :
    (euclideanSpace.linearEquiv K x).1 ⟨w, hw⟩ = x.1 ⟨w, hw⟩ := rfl

@[simp]
theorem linearEquiv_apply_ofIsComplex (x : E₂ K) {w : InfinitePlace K} (hw : IsComplex w) :
    (euclideanSpace.linearEquiv K x).2 ⟨w, hw⟩ = x.2 ⟨w, hw⟩ := rfl

instance : Nontrivial (E₂ K) := (euclideanSpace.linearEquiv K).toEquiv.nontrivial

/-- Docs. -/
protected def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (E₂ K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ ℝ)
    ((Pi.orthonormalBasis fun _ ↦ Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

theorem stdOrthonormalBasis_map_equiv :
    (euclideanSpace.stdOrthonormalBasis K).toBasis.map (euclideanSpace.linearEquiv K) =
      mixedEmbedding.stdBasis K := by ext _ _ <;> rfl

@[simp]
theorem stdOrthonormalBasis_repr_apply (x : E₂ K) (i : index K) :
    (euclideanSpace.stdOrthonormalBasis K).repr x i =
      (stdBasis K).repr (euclideanSpace.linearEquiv K x) i := rfl

theorem measurePreserving_euclideanLinearEquiv :
    MeasurePreserving (euclideanSpace.linearEquiv K) := by
  let e := (euclideanSpace.homeomorph K).toMeasurableEquiv
  convert e.measurable.measurePreserving volume
  erw [← (OrthonormalBasis.addHaar_eq_volume (euclideanSpace.stdOrthonormalBasis K)),
    Homeomorph.toMeasurableEquiv_coe, Basis.map_addHaar _ (euclideanSpace.continuousLinearEquiv K),
    stdOrthonormalBasis_map_equiv, eq_comm, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
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

theorem aux00 {x : E₂ K} (hx : x ∈ X K) :
    0 < mixedEmbedding.norm (euclideanSpace.linearEquiv K x) :=
  lt_iff_le_and_ne.mpr ⟨mixedEmbedding.norm_nonneg _, Ne.symm hx.2⟩

theorem aux0 {x : E₂ K} (hx : x ∈ X₁ K) :
    ∃ c : ℝ, 1 ≤ c ∧ c • x ∈ F₁ K := by
  have : finrank ℚ K ≠ 0 := ne_of_gt finrank_pos
  refine ⟨((mixedEmbedding.norm (euclideanSpace.linearEquiv K x)) ^ (-(finrank ℚ K : ℝ)⁻¹)),
    ?_, ?_⟩
  · refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
    · exact aux00 hx.1
    · exact hx.2
    · aesop
  · refine ⟨?_, ?_⟩
    · rw [X, Set.mem_preimage, _root_.map_smul]
      refine smul_mem_of_mem hx.1 ?_
      refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
      exact mixedEmbedding.norm_nonneg _
      aesop
      exact ne_of_gt (aux00 hx.1)
    · have := aux00 hx.1
      rw [_root_.map_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr]
      rw [← Real.rpow_natCast, ← Real.rpow_mul, neg_mul, inv_mul_cancel, Real.rpow_neg_one,
        inv_mul_cancel]
      exact ne_of_gt (aux00 hx.1)
      aesop
      exact mixedEmbedding.norm_nonneg _
      refine Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _

theorem aux1 (h : IsBounded (F₁ K)) :
    IsBounded (X₁ K) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  obtain ⟨r, hr₁, hr₂⟩ := h.subset_ball_lt 0 0
  refine ⟨r, ?_⟩
  intro x hx
  obtain ⟨c, hc₁, hc₂⟩ := aux0 hx
  have := hr₂ hc₂
  rw [mem_ball_zero_iff] at this ⊢
  rw [← smul_lt_smul_iff_of_pos_left (by linarith : 0 < c)]
  rw [show c • ‖x‖ = ‖c • x‖ by
    rw [norm_smul, Real.norm_eq_abs, abs_eq_self.mpr (by linarith), smul_eq_mul]]
  refine lt_of_lt_of_le this ?_
  refine le_smul_of_one_le_left ?_ ?_
  exact le_of_lt hr₁
  exact hc₁

theorem aux11 : frontier (X₁ K) = F₁ K := by
  unfold X₁ F₁
  let f := Set.indicator (X K)
    (fun x : E₂ K ↦ mixedEmbedding.norm (euclideanSpace.linearEquiv K x))
  let g := Set.indicator (X K) (fun _ ↦ (1 : ℝ))
  have := frontier_le_eq_eq (f := f) (g := g) sorry sorry sorry
  convert this
  · sorry
  · sorry

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

theorem aux20 :
    ∃ s : Set ℝ, IsBounded s ∧ ∀ i, ∀ x ∈ F₁ K,
      (euclideanSpace.stdOrthonormalBasis K).repr x i ∈ s := by
  rsuffices ⟨C₁, C₂, hC₁, hC₂, h⟩ : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 1 ≤ C₂ ∧
      ∀ x ∈ (F₁ K),
        (∀ w, w.val ≠ w₀ → C₁ < ‖x.1 w‖ ∧ ‖x.1 w‖ ≤ C₂) ∧
        (∀ w, w.val ≠ w₀ → C₁ < ‖x.2 w‖ ^ 2 ∧ ‖x.2 w‖ ^ 2 ≤ C₂) := by
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
    obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
    have h : ∀ x ∈ X K, ∀ w : { w // w ≠ w₀ },
      ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r :=
        fun _ h ↦ (pi_norm_lt_iff hr₁).mp  <| mem_ball_zero_iff.mp (hr₂ h.1)
    refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.one_le_exp (le_of_lt hr₁),
      fun x hx ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
    · specialize h x hx.1 ⟨w.val, hw⟩
      rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
      rwa [logMap_apply_F₁_ofIsReal hx hw w.prop, Real.norm_eq_abs] at h
      sorry
      sorry
    · specialize h x hx.1 ⟨w.val, hw⟩
      rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt, Real.log_pow,
        Nat.cast_ofNat]
      rwa [logMap_apply_F₁_ofIsComplex hx hw w.prop, Real.norm_eq_abs] at h
      sorry
      sorry
  let M := max C₂ (C₁ ^ (1 - Fintype.card (InfinitePlace K)))
  refine ⟨Metric.closedBall 0 M, Metric.isBounded_closedBall, fun i x hx  ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  cases i with
  | inl w =>
      by_cases hw : w.1 ≠ w₀
      · rw [stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsReal]
        rw [euclideanSpace.linearEquiv_apply_ofIsReal]
        replace h := ((h x hx).1 w hw).2
        refine le_trans ?_ (le_max_left _ _)
        exact h
      · 
        sorry
  | inr wj =>
      rcases wj with ⟨w, j⟩
      by_cases hw : w.1 ≠ w₀
      · fin_cases j
        · rw [Fin.zero_eta, stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsComplex_fst,
            Real.norm_eq_abs]
          refine le_trans (Complex.abs_re_le_abs _) ?_
          replace h := ((h x hx).2 w hw).2
          refine le_trans ?_ (le_max_left _ _)
          rw [← Real.le_sqrt] at h
          refine le_trans h ?_
          sorry
          exact norm_nonneg _
          sorry
        · rw [Fin.mk_one, stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsComplex_snd,
            Real.norm_eq_abs]
          refine le_trans (Complex.abs_im_le_abs _) ?_
          replace h := ((h x hx).2 w hw).2
          refine le_trans ?_ (le_max_left _ _)
          rw [← Real.le_sqrt] at h
          refine le_trans h ?_
          sorry
          exact norm_nonneg _
          sorry
      · sorry

#exit

  --   let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  --   have := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
  --   obtain ⟨r, hr₁, hr₂⟩ := this
  --   refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.exp_pos _, fun x hx₁ ↦ ?_⟩
  --   have hx₂ : x ≠ 0 := sorry
  --   have hx₃ : (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := sorry
  --   have hx₄ :  ∀ w : { w // w ≠ w₀ }, ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r := by
  --     rw [← pi_norm_lt_iff hr₁, ← mem_ball_zero_iff]
  --     refine hr₂ ?_
  --     have := hx₁.1
  --     rw [X, fundamentalCone, Set.mem_preimage] at this
  --     exact (this.resolve_right (by simp [hx₂])).1

theorem aux2 : IsBounded (F₁ K) := by
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s : Set ℝ, IsBounded s ∧ ∀ i, ∀ x ∈ F₁ K,
    (euclideanSpace.stdOrthonormalBasis K).repr x i ∈ s := sorry
  refine IsBounded.subset (isBoundedOfBoundedCoeff
    (fun i ↦ euclideanSpace.stdOrthonormalBasis K i) hs₁) ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨(euclideanSpace.stdOrthonormalBasis K).repr x i, ?_⟩
    exact hs₂ i x hx
  · simp_rw [OrthonormalBasis.sum_repr]

  -- rsuffices ⟨C, _, hC⟩ : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
  --     ∀ x ∈ (F₁ K),
  --       (∀ w, w.val ≠ w₀ → C₁ < ‖x.1 w‖ ∧ ‖x.1 w‖ < C₂) ∧
  --       (∀ w, w.val ≠ w₀ → C₁ < ‖x.2 w‖ ∧ ‖x.2 w‖ < C₂) := by
  --   let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  --   have := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
  --   obtain ⟨r, hr₁, hr₂⟩ := this
  --   refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.exp_pos _, fun x hx₁ ↦ ?_⟩
  --   have hx₂ : x ≠ 0 := sorry
  --   have hx₃ : (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := sorry
  --   have hx₄ :  ∀ w : { w // w ≠ w₀ }, ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r := by
  --     rw [← pi_norm_lt_iff hr₁, ← mem_ball_zero_iff]
  --     refine hr₂ ?_
  --     have := hx₁.1
  --     rw [X, fundamentalCone, Set.mem_preimage] at this
  --     exact (this.resolve_right (by simp [hx₂])).1

  --   refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  --   · rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
  --     rw [← logMap_apply_F₁_ofIsReal hx₁ hw]
  --     exact hx₄ ⟨w.val, hw⟩
  --     sorry
  --     sorry
  --   · rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
  --     refine lt_trans ?_ (div_two_lt_of_pos hr₁)
  --     rw [← mul_lt_mul_left (zero_lt_two)]
  --     rw [mul_div_cancel₀ _ (two_ne_zero)]
  --     rw [show (2:ℝ) = |2| by norm_num, ← abs_mul]
  --     rw [← logMap_apply_F₁_ofIsComplex hx₁ hw]
  --     exact hx₄ ⟨w.val, hw⟩
  --     sorry
  --     sorry
  -- rw [Metric.isBounded_iff_subset_closedBall 0]
  -- refine ⟨?_, ?_⟩
  -- · sorry
  -- · intro x hx
  --   rw [mem_closedBall_zero_iff, euclideanSpace.norm_apply]
  --   sorry

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

open Submodule Ideal nonZeroDivisors

example :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K : ℝ) / n) atTop
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
  · sorry
  · sorry
  · sorry
  · sorry

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
