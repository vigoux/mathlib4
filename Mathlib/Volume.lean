import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Finset
  NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional MeasureTheory.Measure

open scoped Real ENNReal

namespace NumberField.mixedEmbedding.fundamentalCone

open Classical

noncomputable section

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

variable {K}

def isNormStableAtRealPlaces (s : Set (E K)) : Prop :=
    ∀ x, x ∈ s ↔ ⟨fun w ↦ ‖x.1 w‖, x.2⟩ ∈ s

def isNormStableAtComplexPlaces (s : Set (E K)) : Prop :=
    ∀ x, x ∈ s ↔ ⟨x.1, fun w ↦ ‖x.2 w‖⟩ ∈ s

def isNormStable (s : Set (E K)) : Prop :=
    isNormStableAtRealPlaces s ∧ isNormStableAtComplexPlaces s

variable (K) in
def normVector : (E K) → (InfinitePlace K → ℝ) := fun x w ↦ normAtPlace w x

theorem normVector_normAtRealPlaces_eq_normVector (x : E K) :
    normVector K ⟨fun w ↦ ‖x.1 w‖, x.2⟩ = normVector K x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normVector, normAtPlace_apply_isReal hw, norm_norm]
  · simp_rw [normVector, normAtPlace_apply_isComplex hw]

theorem normVector_normAtComplexPlaces_eq_normVector (x : E K) :
    normVector K ⟨x.1, fun w ↦ ‖x.2 w‖⟩ = normVector K x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normVector, normAtPlace_apply_isReal hw]
  · simp_rw [normVector, normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.abs_ofReal,
      Complex.abs_abs]

theorem normVector_norm_eq_normVector (x : E K) :
    normVector K ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ = normVector K x := by
  rw [← normVector_normAtRealPlaces_eq_normVector x,
    ← normVector_normAtComplexPlaces_eq_normVector ⟨fun w ↦ ‖x.1 w‖, x.2⟩]

theorem isNormStable_iff (s : Set (E K)) :
    isNormStable s ↔ s = normVector K ⁻¹' (normVector K '' s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩⟩
  · ext x
    refine ⟨fun h ↦ Set.subset_preimage_image _ _ h, fun ⟨y, hy₁, hy₂⟩ ↦ ?_⟩
    rw [h.1, h.2] at hy₁ ⊢
    simp_rw [show ∀ w, ‖x.1 w‖ = ‖y.1 w‖ by
      intro w
      rw [← normAtPlace_apply_isReal w.prop, ← normAtPlace_apply_isReal w.prop]
      exact (congr_fun hy₂ w.val).symm]
    simp_rw [show ∀ w, ‖x.2 w‖ = ‖y.2 w‖ by
      intro w
      rw [← normAtPlace_apply_isComplex w.prop, ← normAtPlace_apply_isComplex w.prop]
      exact (congr_fun hy₂ w.val).symm]
    exact hy₁
  · rw [h, Set.mem_preimage, ← normVector_normAtRealPlaces_eq_normVector, Set.mem_preimage]
  · rw [h, Set.mem_preimage, ← normVector_normAtComplexPlaces_eq_normVector, Set.mem_preimage]

private theorem volume_eq_of_isNormStableAtRealPlaces_aux (f : (E K) → ℝ≥0∞)
    (W : Finset {w : InfinitePlace K // w.IsReal}) (hf : Measurable f)
    (a : {w : InfinitePlace K // w.IsReal} → ℝ) (y : {w : InfinitePlace K // w.IsComplex} → ℂ) :
    (∫⋯∫⁻_W, fun x ↦ f ⟨fun w ↦ ‖x w‖, y⟩ ∂fun _ ↦ (volume : Measure ℝ)) a =
      2 ^ W.card *
        (∫⋯∫⁻_W, fun x ↦ f (x, y) ∂fun _ ↦ (volume.restrict (Set.Ioi 0))) fun i ↦ ‖a i‖ := by
  induction W using Finset.induction generalizing a with
  | empty => simp
  | @insert i W hi h_ind =>
      rw [lmarginal_insert _ (by fun_prop) hi]
      have : ∀ (xᵢ : ℝ) i j,
          ‖Function.update a j xᵢ i‖ = Function.update (fun j ↦ ‖a j‖) j ‖xᵢ‖ i :=
        fun _ _ _ ↦ by rw [Function.update_apply, Function.update_apply, apply_ite norm]
      simp_rw [h_ind, this, Real.norm_eq_abs]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.two_ne_top)]
      have : ∀ y, Measurable (fun xᵢ ↦ (∫⋯∫⁻_W, fun x ↦ f (x, y)
          ∂fun x ↦ volume.restrict (Set.Ioi 0))
            (fun j ↦ Function.update (fun j ↦ |a j|) i xᵢ j)) :=
        fun _ ↦ (Measurable.lmarginal _ (by fun_prop)).comp (measurable_update _)
      simp_rw [lintegral_comp_abs (this _)]
      rw [lmarginal_insert _ (by fun_prop) hi, ← mul_assoc, ← pow_succ, card_insert_of_not_mem hi]

theorem volume_eq_of_isNormStableAtRealPlaces (s : Set (E K)) (hs₀ : MeasurableSet s)
    (hs₁ : isNormStableAtRealPlaces s) :
    volume s = 2 ^ NrRealPlaces K * volume (s ∩ {x | ∀ w, 0 < x.1 w}) := by
  have h₁ : Measurable (s.indicator fun _ ↦ (1 : ℝ≥0∞)) :=
    (measurable_indicator_const_iff 1).mpr hs₀
  have h₂ : MeasurableSet (s ∩ {x | ∀ (w : { w // w.IsReal }), 0 < x.1 w}) := by
    convert_to MeasurableSet (s ∩ (⋂ w : { w // w.IsReal }, {x | 0 < x.1 w}))
    · ext; simp
    · exact hs₀.inter (MeasurableSet.iInter fun _ ↦
        measurableSet_lt measurable_const (by convert (measurable_pi_apply _).comp measurable_fst))
  have h₃ : ∀ x y, s.indicator (fun _ ↦ (1: ℝ≥0∞)) (x, y) =
      s.indicator (fun _ ↦ 1) (fun w ↦ ‖x w‖, y) := fun x y ↦ by
    by_cases h : (x, y) ∈ s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hs₁ (x, y)).mp h)]
    · rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem ((hs₁ (x, y)).not.mp h)]
  have h₄ := volume_eq_of_isNormStableAtRealPlaces_aux (s.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    Finset.univ h₁ 0
  simp_rw [lmarginal_univ, ← measure_restrict_pi_pi , ← volume_pi] at h₄
  rw [← setLIntegral_one, ← setLIntegral_one, ← lintegral_indicator _ hs₀, ← lintegral_indicator _
    h₂, volume_eq_prod, lintegral_prod_symm _ h₁.aemeasurable]
  simp_rw (config := {singlePass := true}) [h₃, h₄]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.two_ne_top), NrRealPlaces, Fintype.card,
    lintegral_lintegral_symm (measurable_swap_iff.mp (by convert h₁)).aemeasurable,
    restrict_prod_eq_prod_univ, ← lintegral_indicator _ ((MeasurableSet.univ_pi
    (fun _ ↦ measurableSet_Ioi)).prod MeasurableSet.univ), Set.indicator_indicator,
    show (Set.univ.pi fun i ↦ Set.Ioi 0) ×ˢ Set.univ ∩ s = s ∩ {x | ∀ w, 0 < x.1 w} by
    ext; simp [and_comm]]

open ENNReal in
private theorem volume_eq_of_isNormStableAtComplexPlaces_aux
    (f : ({w : InfinitePlace K // w.IsReal} → ℝ) ×
      ({w : InfinitePlace K // w.IsComplex} → ℝ) → ℝ≥0∞)
    (W : Finset {w : InfinitePlace K // w.IsComplex}) (hf : Measurable f)
    (a : {w : InfinitePlace K // w.IsComplex} → ℂ) (x : {w : InfinitePlace K // w.IsReal} → ℝ) :
    (∫⋯∫⁻_W, fun y ↦ f ⟨x, fun w ↦ ‖y w‖⟩ ∂fun _ ↦ (volume : Measure ℂ)) a =
      (2 * NNReal.pi) ^ W.card * (∫⋯∫⁻_W, (fun y ↦ (∏ i ∈ W, (y i).toNNReal) * f ⟨x, y⟩)
        ∂fun _ ↦ (volume.restrict (Set.Ici (0 : ℝ)))) (fun i ↦ ‖a i‖) := by
  induction W using Finset.induction generalizing a with
  | empty => simp
  | @insert i W hi h_ind =>
      rw [lmarginal_insert _ (by fun_prop) hi]
      have : ∀ (xᵢ : ℂ) i j,
          ‖Function.update a j xᵢ i‖ = Function.update (fun j ↦ ‖a j‖) j ‖xᵢ‖ i :=
        fun _ _ _ ↦ by rw [Function.update_apply, Function.update_apply, apply_ite norm]
      simp_rw [h_ind, this]
      rw [lintegral_const_mul' _ _ (by convert coe_ne_top)]
      have : ∀ x, Measurable (fun yᵢ ↦ (∫⋯∫⁻_W, fun y ↦ (∏ i ∈ W, (y i).toNNReal) * f (x, y)
          ∂fun x ↦ volume.restrict (Set.Ici 0))
            (fun j ↦ Function.update (fun j ↦ ‖a j‖) i yᵢ j)) :=
        fun _ ↦ (Measurable.lmarginal _ (by fun_prop)).comp (measurable_update _)
      simp_rw [Complex.lintegral_norm (this _)]
      rw [lmarginal_insert _ (by fun_prop) hi, ← mul_assoc, ← pow_succ, card_insert_of_not_mem hi,
        restrict_Ioi_eq_restrict_Ici]
      congr!
      rw [← lmarginal_const_smul' _ _ coe_ne_top, lmarginal_update_of_not_mem
       (Measurable.const_smul (by fun_prop) _) hi, lmarginal_update_of_not_mem (by fun_prop) hi]
      simp_rw [Finset.prod_insert hi, Function.comp, Pi.smul_apply, smul_eq_mul,
        Function.update_same, ENNReal.coe_mul, mul_assoc]

theorem volume_eq_of_isNormStableAtComplexPlaces (s : Set (E K)) (hs₀ : MeasurableSet s)
    (hs₁ : isNormStableAtComplexPlaces s) :
    volume s = (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ x in (fun x : (E K) ↦ (x.1, fun w ↦ (‖x.2 w‖ : ℝ))) '' s, ∏ w, (x.2 w).toNNReal := by
  set s₀ := (fun x : (E K) ↦ (x.1, fun w ↦ (‖x.2 w‖ : ℝ))) '' s with def_s₀
  have h₄ := volume_eq_of_isNormStableAtComplexPlaces_aux (s₀.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    Finset.univ ?_ 0
  simp_rw [lmarginal_univ, ← measure_restrict_pi_pi , ← volume_pi] at h₄

  rw [← setLIntegral_one, ← lintegral_indicator _ hs₀, volume_eq_prod, lintegral_prod]

  have h₃ : ∀ x y, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x, y) =
      s₀.indicator (fun _ ↦ 1) ⟨x, fun w ↦ ‖y w‖⟩ := by
    intro x y
    by_cases h : (x, y) ∈ s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
      refine ⟨(x, y), h, rfl⟩
    · rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem]
      intro h'
      sorry
  simp_rw (config := {singlePass := true}) [h₃, h₄]

  rw [lintegral_const_mul' _ _, NrComplexPlaces, Fintype.card,
    lintegral_lintegral, restrict_prod_eq_univ_prod, ← lintegral_indicator]
  rw [Set.indicator_mul, Set.indicator_indicator]

  have : s₀ ⊆ (Set.univ ×ˢ Set.univ.pi fun i ↦ Set.Ici 0) := sorry

  rw [← lintegral_indicator]

  congr! with _ _ x
  by_cases hx : x ∈ s₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Set.indicator_of_mem, mul_one,
      ENNReal.coe_finset_prod]
    exact Set.mem_inter (this hx) hx
    exact this hx
  · have : x ∉ (Set.univ ×ˢ Set.univ.pi fun i ↦ Set.Ici 0) ∩ s₀ := fun h ↦ hx h.2
    rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem this, mul_zero]

theorem volume_eq_of_isNormStable (s : Set (E K))
    (hs₀ : MeasurableSet s) (hs₁ : isNormStable s) :
    volume s = 2 ^ NrRealPlaces K * (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ x in (normVector K '' s), (∏ w : {w // IsComplex w}, (x w.val).toNNReal) := by
  rw [volume_eq_of_isNormStableAtRealPlaces, volume_eq_of_isNormStableAtComplexPlaces]
  sorry



#exit

def updateAtPlace (x : E K) (w : InfinitePlace K) : E K := by
  exact if hw : w.IsReal then ⟨Function.update x.1 ⟨w, hw⟩ (normAtPlace w x), x.2⟩
    else ⟨x.1, Function.update x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩ (normAtPlace w x)⟩

def isNormStableAt (s : Set (E K)) (w : InfinitePlace K) : Prop :=
    ∀ x, x ∈ s ↔ updateAtPlace x w ∈ s

example {s : Set (E K)} {W : Finset (InfinitePlace K)} (hs : ∀ w ∈ W, isNormStableAt s w)
    {x y : E K} (h₁ : ∀ w, w ∉ W → )

theorem mem_iff_mem_of_isNormStableAt {s : Set (E K)} {w : InfinitePlace K}
    (hs : isNormStableAt s w) {x y : E K} (h : updateAtPlace x w = updateAtPlace y w) :
    x ∈ s ↔ y ∈ s := by
  rw [hs x, hs y, h]

variable (K) in
def normVector : (E K) → (InfinitePlace K → ℝ) := fun x w ↦ normAtPlace w x

theorem normVector_updateAtPlace (x : E K) (w : InfinitePlace K) :
    normVector K (updateAtPlace x w) = normVector K x := sorry

def isNormStable (s : Set (E K)) : Prop := s = normVector K ⁻¹' (normVector K '' s)

theorem isNormStable_iff (s : Set (E K)) :
    isNormStable s ↔ ∀ w, isNormStableAt s w := by
  refine ⟨fun h w x ↦ ?_, ?_⟩
  · rw [h, h, Set.mem_preimage, Set.mem_preimage, normVector_updateAtPlace ]
  · intro h
    refine le_antisymm ?_ ?_
    · exact Set.subset_preimage_image _ _
    · intro x hx
      rw [Set.mem_preimage] at hx

      obtain ⟨y, hy₁, hy₂⟩ := hx

      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      rw [h w]
      rw [h w] at hy₁


#exit

theorem isNormStable_iff (s : Set (E K)) :
    isNormStable s ↔ ∀ x y, normVector K x = normVector K y → (x ∈ s ↔ y ∈ s) := by
  refine ⟨?_, ?_⟩
  · intro h x y hxy
    rw [h, Set.mem_preimage, Set.mem_preimage, hxy]
  · intro h
    ext x
    rw [Set.mem_preimage]
    specialize h x ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ ?_
    sorry


#exit

theorem normStable_iff (s : Set (E K)) :
    normStable s ↔ ∀ x y, normVector K x = normVector K y → (x ∈ s ↔ y ∈ s) := by
  refine ⟨?_, ?_⟩
  · intro h x y hxy
    rw [h, Set.mem_preimage, Set.mem_preimage, hxy]
  · intro h
    ext x
    rw [Set.mem_preimage]
    specialize h x ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ sorry
    sorry



open Set in
theorem lintegral_comp_abs {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f |x| = 2 * ∫⁻ x in Ioi 0, f x := by
  calc
    _ = (∫⁻ x in Iic 0, f |x|) + ∫⁻ x in Ioi 0, f |x| := by
      rw [← lintegral_union measurableSet_Ioi (Iic_disjoint_Ioi le_rfl), Iic_union_Ioi,
        setLIntegral_univ]
    _ = (∫⁻ x in Iio 0, f (-x)) + ∫⁻ x in Ioi 0, f x := by
      rw [restrict_Iio_eq_restrict_Iic]
      congr 1
      · refine setLIntegral_congr_fun measurableSet_Iic ?_
        exact Filter.eventually_of_forall fun x hx ↦ by rw [abs_of_nonpos (by convert hx)]
      · refine setLIntegral_congr_fun measurableSet_Ioi ?_
        exact Filter.eventually_of_forall fun x hx ↦ by rw [abs_of_pos (by convert hx)]
    _ = 2 * ∫⁻ x in Ioi 0, f x := by
      rw [two_mul, show Iio (0 : ℝ) = (fun x ↦ -x) ⁻¹' Ioi 0 by simp,
        ← (setLIntegral_map measurableSet_Ioi hf measurable_neg), Measure.map_neg_eq_self]

theorem multiple_step₁ {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ENNReal)
    (hf : Measurable f) (s : Finset ι) (a : ι → ℝ) :
    (∫⋯∫⁻_s, fun z ↦ (f fun i ↦ ‖z i‖) ∂fun _ ↦ (volume : Measure ℝ)) a =
      2 ^ s.card * (∫⋯∫⁻_s, f ∂fun _ ↦ (volume.restrict (Set.Ioi (0 : ℝ)))) fun i ↦ ‖a i‖ := by
  induction s using Finset.induction generalizing a with
  | empty => simp
  | insert hi h_ind =>
      have h₀ : ∀ (xᵢ : ℝ) (i j : ι),
          ‖Function.update a j xᵢ i‖ = Function.update (fun j ↦ ‖a j‖) j ‖xᵢ‖ i :=
        fun _ _ _ ↦ by rw [Function.update_apply, Function.update_apply, apply_ite norm]
      rw [lmarginal_insert _ ?_ hi]
      swap;
      · refine hf.comp (measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).norm)
      simp_rw [h_ind, h₀]
      sorry

example (s : Set (E K)) (hs₀ : Measurable s) (hs₁ : normStable s) :
    volume s = 2 ^ NrRealPlaces K * volume (s ∩ {x | ∀ w, 0 < x.1 w}) := by
  rw [← setLIntegral_one, ← setLIntegral_one, ← lintegral_indicator, ← lintegral_indicator,
    Measure.volume_eq_prod, lintegral_prod, lintegral_prod, volume_pi,
    lintegral_eq_lmarginal_univ (0 : {w // IsReal w} → ℝ)]
  have : ∀ x y, s.indicator (fun _ ↦ (1 : ENNReal)) (x, y) = s.indicator (fun _ ↦ 1)
    ⟨fun w ↦ ‖x w‖, fun w ↦ y w⟩ := sorry
  simp_rw (config := {singlePass := true}) [this]
  have := multiple_step₁
    (fun x ↦ ∫⁻ y : {w : InfinitePlace K // w.IsComplex} → ℂ,
      s.indicator (fun _ ↦ (1 : ENNReal)) (fun w ↦ x w, fun w ↦ y w)) sorry Finset.univ 0
  rw [this]
  rw [lmarginal_univ, ← measure_restrict_pi_pi]
  rw [← lintegral_indicator]
  · congr! with _ x
    by_cases hx : x ∈ Set.univ.pi fun _ ↦ Set.Ioi 0
    · have : s ∩ {x | ∀ (w : { w // w.IsReal }), 0 < x.1 w} = s := by
        refine Set.inter_eq_left.mpr ?_
        intro _ h w
        -- WTF??
      simp_rw [Set.indicator_of_mem hx, this]
    · have : ∀ y, (x, y) ∉ s ∩ {x | ∀ (w : { w // w.IsReal }), 0 < x.1 w} := by
        rintro _ ⟨_, h⟩
        rw [Set.mem_univ_pi, not_forall] at hx
        obtain ⟨w, hw⟩ := hx
        have := h w
        rw [Set.not_mem_Ioi] at hw
        linarith
      simp_rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem (this _), lintegral_zero]

variable {K} in
def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) :=
  Fintype.equivOfCardEq
    (by rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank])

def logRepr : (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) := fun x w ↦
  if hw : w = w₀ then mixedEmbedding.norm ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩
    else (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex equivFinRank.symm).repr
        (logMap ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩) ⟨w, hw⟩

def paramBox : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

theorem image_normLessThanOne :
    (logRepr K ∘ normVector K) '' (normLessThanOne K) = paramBox K := sorry

theorem preimage_paramBox :
    (logRepr K ∘ normVector K)⁻¹' (paramBox K) = normLessThanOne K := sorry

example :
    closure (normLessThanOne K) ⊆ (logRepr K ∘ normVector K)⁻¹' (closure (paramBox K)) := by
  rw [← preimage_paramBox]
  refine Continuous.closure_preimage_subset ?_ _
  sorry -- not continuous everywhere but...

example :
    (logRepr K ∘ normVector K)⁻¹' (interior (paramBox K)) ⊆ interior (normLessThanOne K) := by
  rw [← preimage_paramBox]
  -- ContinuousOn.preimage_interior_subset_interior_preimage
  sorry




#exit


def realSpaceToMixedSpace : (InfinitePlace K → ℝ) →ₐ[ℝ] (E K) where
  toFun := fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

def mixedSpaceToRealSpace : (E K) →* (InfinitePlace K → ℝ) where
  toFun := fun x w ↦ normAtPlace w x
  map_one' := sorry
  map_mul' := sorry

theorem mixedSpaceToRealSpace_apply (x : E K) :
    mixedSpaceToRealSpace x = fun w ↦ normAtPlace w x := rfl

theorem realSpaceToMixedSpace_apply (x : InfinitePlace K → ℝ) :
    realSpaceToMixedSpace x = ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩ := rfl

theorem mixedSpaceToRealSpaceToMixedSpace_apply (x : E K) :
    realSpaceToMixedSpace (mixedSpaceToRealSpace x) =
      ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ := by
  simp_rw [mixedSpaceToRealSpace_apply, realSpaceToMixedSpace_apply,
    normAtPlace_apply_isReal (Subtype.prop _), normAtPlace_apply_isComplex (Subtype.prop _)]

def updateByNormAtPlace (x : E K) (w : InfinitePlace K) : E K := by
  exact if hw : IsReal w then ⟨Function.update x.1 ⟨w, hw⟩ (normAtPlace w x), x.2⟩ else
    ⟨x.1, Function.update x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩ (normAtPlace w x)⟩

theorem preimage_eq_self_iff (s : Set (E K)) :
    (realSpaceToMixedSpace ∘ mixedSpaceToRealSpace)⁻¹' s = s ↔
      ∀ x, (x ∈ s ↔ ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ ∈ s) := by
  refine ⟨?_, ?_⟩
  · intro hs x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rwa [← hs, Set.mem_preimage, Function.comp_apply,
        mixedSpaceToRealSpaceToMixedSpace_apply] at hx
    · rwa [← mixedSpaceToRealSpaceToMixedSpace_apply, ← Set.mem_preimage, ← Set.mem_preimage,
        ← Set.preimage_comp, hs] at hx
  · intro hx
    ext
    rw [Set.mem_preimage, Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply, ← hx]

theorem volume_eq_of_preimage_eq_self (s : Set (E K)) (hs₀ : MeasurableSet s)
    (hs₁ : (realSpaceToMixedSpace ∘ mixedSpaceToRealSpace)⁻¹' s = s)
    (T : Finset {w : InfinitePlace K // w.IsReal}) :
    volume s = 2 ^ Finset.card T * (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ x in realSpaceToMixedSpace ⁻¹' s ∩ {x | ∀ w, 0 < x w},
        (∏ w : {w // IsComplex w}, (x w.val).toNNReal) := by sorry

def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def logRepr (x : InfinitePlace K → ℝ) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex equivFinRank.symm).repr
        (logMap (realSpaceToMixedSpace x))

theorem logRepr_apply (x : InfinitePlace K → ℝ) (i : {w : InfinitePlace K // w ≠ w₀}):
    logRepr x i =
      (((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K)).repr
        (logMap (realSpaceToMixedSpace x))) (equivFinRank i) := by
  simp [logRepr]

theorem logRepr_smul {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realSpaceToMixedSpace x) ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logRepr (c • x) = logRepr x := by
  simp_rw [logRepr, ← logMap_smul hx hc, realSpaceToMixedSpace_apply, Prod.smul_mk, Pi.smul_def,
    smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]

def mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, w (fundSystem K (equivFinRank i)) ^ (c i)

theorem mapToUnitsPow₀_apply (c₀ : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ c₀ =  fun w ↦ ∏ i, w (fundSystem K (equivFinRank i)) ^ (c₀ i) := rfl

theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ (K := K)) := by
  refine continuous_pi fun w ↦ continuous_finset_prod _ fun i _ ↦ ?_
  exact continuous_const.rpow (continuous_apply i) fun _ ↦ by left; simp

theorem norm_mapToUnitsPow₀ (c₀ : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realSpaceToMixedSpace (mapToUnitsPow₀ c₀)) = 1 := by
  simp_rw [mapToUnitsPow₀_apply, ← Finset.prod_fn, map_prod, mixedEmbedding.norm_apply]
  sorry

theorem logRepr_mapToUnitPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
  logRepr (mapToUnitsPow₀ c) = c := sorry

variable (K) in
def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ |c w₀| ^ (finrank ℚ K : ℝ)⁻¹ • mapToUnitsPow₀ (fun w ↦ c w)
  invFun := fun x w ↦ if hw : w = w₀ then mixedEmbedding.norm (realSpaceToMixedSpace x)
    else logRepr x ⟨w, hw⟩
  source := Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ
  target := Set.univ.pi fun _ ↦ Set.Ioi 0
  map_source' := by
    intro x hx
    rw [Set.mem_univ_pi]
    intro w
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_Ioi]
    refine mul_pos ?_ ?_
    · sorry
    · sorry
  map_target' := by
    intro x hx
    rw [Set.mem_univ_pi]
    intro w
    rw [Set.mem_ite_univ_right, Set.mem_Ioi]
    intro hw
    dsimp only
    split_ifs
    sorry
  left_inv' := by
    intro c hc
    ext w
    refine dite_eq_iff'.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [_root_.map_smul, mixedEmbedding.norm_smul, h, norm_mapToUnitsPow₀, mul_one,
        abs_eq_self.mpr]
      sorry
      sorry
    · rw [logRepr_smul, logRepr_mapToUnitPow₀]
      sorry
      sorry
  right_inv' := by
    intro x hx
    simp only [↓reduceDIte, ne_eq, Subtype.coe_eta, dite_eq_ite]
    have : x = mixedEmbedding.norm (realSpaceToMixedSpace x) ^ (finrank ℚ K : ℝ)⁻¹ •
      ((mixedEmbedding.norm (realSpaceToMixedSpace x) ^ finrank ℚ K) • x) := sorry
    nth_rewrite 4 [this]
    sorry
  open_source := by
    dsimp only
    refine isOpen_set_pi Set.finite_univ fun _ _ ↦ ?_
    split_ifs
    exact isOpen_Ioi
    exact isOpen_univ
  open_target := by
    dsimp only
    refine isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
  continuousOn_toFun := by
    intro x hx
    dsimp only
    sorry
  continuousOn_invFun := sorry

theorem mapToUnitsPow_source :
    (mapToUnitsPow K).source = Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ := rfl

theorem mapToUnitsPow_target :
    (mapToUnitsPow K).target = Set.univ.pi fun _ ↦ Set.Ioi 0 := rfl

variable (K) in
def paramBox : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

theorem image_paramBox :
    mapToUnitsPow K '' (paramBox K) =
      realSpaceToMixedSpace⁻¹' (normLessThanOne K) ∩ {x | ∀ w, 0 < x w} := sorry

variable (K) in
abbrev upperSet : Set (E K) :=
    mixedSpaceToRealSpace⁻¹' (mixedSpaceToRealSpace '' (closure (normLessThanOne K)))

example : closure (normLessThanOne K) ⊆ upperSet K := by
  exact Set.subset_preimage_image _ _

example : realSpaceToMixedSpace⁻¹' (upperSet K) ∩ {x | ∀ w, 0 < x w} ⊆
      mapToUnitsPow K '' (closure (paramBox K)) := by
  rw [upperSet]
  rw?

#exit

variable (K) in
def upperSet : Set (E K) :=
    mixedSpaceToRealSpace⁻¹' (mapToUnitsPow K '' (closure (paramBox K)))

theorem stable_iff (s : Set (E K)) :
    (realSpaceToMixedSpace ∘ mixedSpaceToRealSpace)⁻¹' s = s ↔
      ∀ x, (x ∈ s ↔ ⟨fun w ↦ ‖x.1 w‖, fun w ↦ ‖x.2 w‖⟩ ∈ s) := by
  refine ⟨?_, ?_⟩
  · intro hs x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rwa [← hs, Set.mem_preimage, Function.comp_apply,
        mixedSpaceToRealSpaceToMixedSpace_apply] at hx
    · rwa [← mixedSpaceToRealSpaceToMixedSpace_apply, ← Set.mem_preimage, ← Set.mem_preimage,
        ← Set.preimage_comp, hs] at hx
  · intro hx
    ext
    rw [Set.mem_preimage, Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply, ← hx]

theorem stability (t : Set (InfinitePlace K → ℝ)) :
    (realSpaceToMixedSpace ∘ mixedSpaceToRealSpace)⁻¹' (mixedSpaceToRealSpace⁻¹' t) =
      mixedSpaceToRealSpace⁻¹' t := by
  rw [stable_iff]
  intro x
  rw [Set.mem_preimage, Set.mem_preimage]
  simp [mixedSpaceToRealSpace_apply, normAtPlace]

theorem a_good_name (s : Set (InfinitePlace K → ℝ)) (hs : ∀ x ∈ s, 0 ≤ x) :
    (mixedSpaceToRealSpace ∘ realSpaceToMixedSpace) ⁻¹' s = s := by
  ext x
  rw [Set.mem_preimage]
  rw [Function.comp_apply]
  rw [mixedSpaceToRealSpace_apply]
  rw [realSpaceToMixedSpace_apply]
  sorry

example : realSpaceToMixedSpace⁻¹' (upperSet K) ⊆
    mapToUnitsPow K '' (closure (paramBox K)) := by
  rw [upperSet]
  rw [Set.preimage_preimage]
  rw [← Function.comp_def]
  rw [a_good_name]
  sorry

example : closure (normLessThanOne K) ⊆ upperSet K := by
  rw [upperSet]
  have := PartialHomeomorph.preimage_closure (mapToUnitsPow K).symm (paramBox K)
  rw [PartialHomeomorph.symm_source] at this
