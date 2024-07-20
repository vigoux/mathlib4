import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Finset
  NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional MeasureTheory.Measure

open scoped Real ENNReal ComplexOrder Classical

namespace NumberField.mixedEmbedding.fundamentalCone

noncomputable section

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

variable {K}

def isNormStableAtRealPlaces (s : Set (E K)) : Prop :=
    ∀ x, x ∈ s ↔ ⟨fun w ↦ ‖x.1 w‖, x.2⟩ ∈ s

def nonnegAtRealPlaces : Set (E K) := {x : E K | ∀ w, 0 ≤ x.1 w}

def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable (K)

def mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, w (fundSystem K (equivFinRank i)) ^ (c i)

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := sorry

local notation "F" K => (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

@[simps apply source target]
def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ |c w₀| ^ (finrank ℚ K : ℝ)⁻¹ • mapToUnitsPow₀ K (fun w ↦ c w)
  invFun := sorry
  source := Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ
  target := Set.univ.pi fun _ ↦ Set.Ioi 0
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

theorem mapToUnitsPow_nonneg (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 ≤ mapToUnitsPow K c w  := by
  rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul]
  refine mul_nonneg ?_ ?_
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact (mapToUnitsPow₀_pos _ _ _).le

theorem mapToUnitsPow_zero_iff (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    mapToUnitsPow K c w = 0 ↔ c w₀ = 0 := by
  simp_rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
    ne_of_gt (mapToUnitsPow₀_pos _ _ _), or_false, Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _),
    abs_eq_zero, and_iff_left_iff_imp, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ← ne_eq]
  intro _
  exact ne_of_gt finrank_pos

@[simps! apply symm_apply source target]
def marcus₁ : PartialHomeomorph (F K) (F K) :=
  PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _)

theorem marcus₁_image_prod (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    marcus₁ K '' (s ×ˢ t) = (mapToUnitsPow K '' s) ×ˢ t := by
  ext; aesop

local notation "G" K => ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

@[simps apply symm_apply]
def marcus₂ : Homeomorph (F K) (G K) where
  toFun := fun x ↦ (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩)
  invFun := fun x ↦ ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩
  left_inv _ := by aesop
  right_inv _ := by
    simp_rw [dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]
  continuous_toFun := by dsimp only; fun_prop
  continuous_invFun := by
    dsimp only
    rw [continuous_prod_mk]
    refine ⟨?_, ?_⟩
    · rw [continuous_pi_iff]
      intro w
      by_cases hw : IsReal w
      · simp_rw [dif_pos hw]
        fun_prop
      · simp_rw [dif_neg hw]
        fun_prop
    · fun_prop

def marcus₂'_symm : (G K) ≃ᵐ (F K) := by
  refine MeasurableEquiv.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ _)) ?_
  refine MeasurableEquiv.trans MeasurableEquiv.prodAssoc.symm ?_
  refine MeasurableEquiv.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm))
    (MeasurableEquiv.refl _)))
    (MeasurableEquiv.refl _))
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm
    (MeasurableEquiv.refl _))

theorem volume_preserving_marcus₂_symm : MeasurePreserving (marcus₂ K).symm := by
  change MeasurePreserving (marcus₂'_symm K) volume volume
  exact MeasurePreserving.trans ((MeasurePreserving.id volume).prod
      (volume_preserving.arrowProdEquivProdArrow ℝ ℝ {w : InfinitePlace K // IsComplex w})) <|
    MeasurePreserving.trans (volume_preserving.prodAssoc.symm) <|
      MeasurePreserving.trans
        (((MeasurePreserving.id volume).prod (volume_preserving.arrowCongr' _ (MeasurableEquiv.refl ℝ)
          (MeasurePreserving.id volume))).prod (MeasurePreserving.id volume))
      <| ((volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
        (fun w : InfinitePlace K ↦ IsReal w)).symm).prod (MeasurePreserving.id volume)

def marcus₃ : PartialHomeomorph (F K) (E K) :=
  (marcus₂ K).toPartialHomeomorph.trans <|
    (PartialHomeomorph.refl _).prod <| PartialHomeomorph.pi fun _ ↦ Complex.polarCoord.symm

@[simp]
theorem marcus₃_apply (x : F K) :
    marcus₃ K x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := by
  simp_rw [marcus₃, PartialHomeomorph.coe_trans, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, Function.comp_apply, id_eq,  Homeomorph.toPartialHomeomorph_apply,
    marcus₂_apply, PartialHomeomorph.pi, PartialHomeomorph.symm_toPartialEquiv,
    PartialHomeomorph.mk_coe, PartialEquiv.pi_apply, PartialHomeomorph.coe_coe_symm]

-- Probably merge with volume_marcus₃_set_prod_set
theorem lintegral_marcus₃ (f : (E K) → ENNReal) :
    ∫⁻ x, f x = ∫⁻ x, (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) * f (marcus₃ K x) := by
  rw [← (volume_preserving_marcus₂_symm K).lintegral_comp]
  simp only [marcus₂_symm_apply, Subtype.coe_eta, ENNReal.coe_finset_prod, marcus₃_apply]
  simp_rw [dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]
  rw [volume_eq_prod, volume_eq_prod, lintegral_prod, lintegral_prod]
  congr with x
  dsimp only
  all_goals sorry

@[simp]
theorem marcus₃_symm_apply (x : E K) :
    (marcus₃ K).symm x =
      ⟨fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else
        ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖, fun w ↦ Complex.arg (x.2 w)⟩ := by
  simp [marcus₃, Complex.polarCoord, Complex.abs_eq_sqrt_sq_add_sq]

theorem marcus₃_source : (marcus₃ K).source =
    (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [marcus₃]
  rw [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.prod_toPartialEquiv,
    PartialHomeomorph.refl_partialEquiv, PartialHomeomorph.pi_toPartialEquiv,
    PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source]
  rw [Homeomorph.toPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    Homeomorph.toPartialHomeomorph_apply, PartialEquiv.prod_source, PartialEquiv.refl_source]
  rw [PartialEquiv.pi_source, PartialEquiv.symm_source, Set.univ_inter]
  rw [marcus₂]
  simp
  rw [Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter]
  rw [Complex.polarCoord_target]
  ext
  simp [forall_and]

theorem marcus₃_target :
    (marcus₃ K).target = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  rw [marcus₃]
  simp [Complex.polarCoord_source]

def full_marcus : PartialHomeomorph (F K) (E K) := by
  refine PartialHomeomorph.trans (marcus₁ K) (marcus₃ K)

theorem full_marcus_source :
    (full_marcus K).source =
      (Set.univ.pi fun i ↦ if i = w₀ then Set.Ioi 0 else Set.univ) ×ˢ
        Set.univ.pi fun _ ↦ Set.Ioo (-π) π := by
  simp only [full_marcus, PartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
    marcus₁_source, PartialHomeomorph.toFun_eq_coe]
  let U : Set ℝ := if ∃ w : InfinitePlace K, IsComplex w then {0}ᶜ else Set.univ
  have : (marcus₁ K) ⁻¹' (marcus₃ K).source =
      (Set.univ.pi fun w ↦ if w = w₀ then U else Set.univ) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
    ext x
    simp_rw [marcus₃_source, Set.mem_preimage, marcus₁_apply, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_ite_univ_left, not_isReal_iff_isComplex,
      and_congr_left_iff, Set.mem_ite_univ_right, Set.mem_Ioi, lt_iff_le_and_ne,
      mapToUnitsPow_nonneg, true_and, ne_comm (a := (0:ℝ)), ne_eq, mapToUnitsPow_zero_iff]
    simp_rw [forall_eq]
    intro _
    dsimp only [U]
    by_cases hc : ∃ w : InfinitePlace K, IsComplex w
    · obtain ⟨w, hw⟩ := hc
      have : (∀ (z : InfinitePlace K), z.IsComplex → ¬ x.1 w₀ = 0) ↔ x.1 w₀ ≠ 0 :=
        ⟨fun h ↦ h w hw, fun h _ _ ↦ h⟩
      rw [this, if_pos, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨w, hw⟩
    · have : (∀ (z : InfinitePlace K), z.IsComplex → ¬ x.1 w₀ = 0) := by
        rw [not_exists] at hc
        exact fun z a _ ↦ hc z a
      simp [this]
  rw [this]
  rw [Set.prod_inter_prod, Set.univ_inter]
  rw [← Set.pi_inter_distrib]
  congr! 3
  dsimp only [U]
  split_ifs <;> aesop

theorem full_marcus_target :
    (full_marcus K).target =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Complex.slitPlane) := by
  simp_rw [full_marcus, PartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_target,
    marcus₃_target, PartialHomeomorph.coe_coe_symm, marcus₁_target]
  have : (marcus₃ K).symm ⁻¹' (Set.univ.pi fun x ↦ Set.Ioi 0) ×ˢ Set.univ =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ {0}ᶜ) := by
    ext
    simp_rw [Set.mem_preimage, marcus₃_symm_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      true_implies, and_true, Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun h w ↦ ?_⟩
    · have := h w
      rwa [dif_pos w.prop] at this
    · have := h w
      rwa [dif_neg (not_isReal_iff_isComplex.mpr w.prop), norm_pos_iff] at this
    · by_cases hw : IsReal w
      · rw [dif_pos hw]
        exact h.1 ⟨w, hw⟩
      · rw [dif_neg hw, norm_pos_iff]
        exact h.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩
  rw [this, Set.prod_inter_prod, Set.univ_inter]
  rw [← Set.pi_inter_distrib]
  have : Complex.slitPlane ∩ {0}ᶜ = Complex.slitPlane := by simp
  simp_rw [this]

def normVector : (E K) → (InfinitePlace K → ℝ) := fun x w ↦ normAtPlace w x

theorem normVector_full_marcus_apply (x : F K) :
    normVector K (full_marcus K x) = mapToUnitsPow K x.1 := by
  unfold  normVector
  simp [full_marcus, marcus₃]
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw]
    simp
    sorry
  · rw [normAtPlace_apply_isComplex hw]
    simp [PartialHomeomorph.pi_apply, Complex.polardCoord_symm_abs]
    sorry

theorem marcus₃_prod_pi (s : Set (InfinitePlace K → ℝ)) (hs₁ : ∀ x, x ∈ s ↔ (fun w ↦ ‖x w‖) ∈ s) :
    marcus₃ K '' (s ×ˢ Set.univ.pi fun _ ↦ Set.Ioc (-π) π) =
      {x : E K | (fun w ↦ normAtPlace w x) ∈ s} := by
  ext x
  simp_rw [marcus₃_apply]
  simp_rw [Set.mem_image, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, ⟨hy₁, _⟩, rfl⟩ := h
    refine Set.mem_setOf.mpr ?_
    have := (hs₁ y.1).mp hy₁
    convert this with w
    obtain hw | hw := isReal_or_isComplex w
    · rw [normAtPlace_apply_isReal hw]
    · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.polardCoord_symm_abs,
        Real.norm_eq_abs]
  · refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      exact fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else
        ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
      exact fun w ↦ Complex.arg (x.2 w)
    · rw [hs₁]
      convert_to (fun w ↦ normAtPlace w x) ∈ s
      · ext w
        by_cases hw : IsReal w
        · simp_rw [dif_pos hw, normAtPlace_apply_isReal hw]
        · simp_rw [dif_neg hw, norm_norm,
            normAtPlace_apply_isComplex (not_isReal_iff_isComplex.mp hw)]
      · exact h
    · exact fun w ↦ Complex.arg_mem_Ioc (x.2 w)
    · ext w
      · simp_rw [dif_pos w.prop]
      · simp [dif_neg (not_isReal_iff_isComplex.mpr w.prop), normAtPlace_apply_isComplex w.prop]

theorem image_by_marcus₃ (s : Set (E K)) (h₁ : ∀ x ∈ s, ∀ w, 0 ≤ x.1 w)
    (h₂ : ∀ x, x ∈ s ↔ ⟨fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖⟩ ∈ s) :
    s = marcus₃ K '' ((normVector K '' s) ×ˢ Set.univ.pi fun _ ↦ Set.Ioc (-π) π) := by
  rw [marcus₃_prod_pi]
  sorry
  sorry

def box₁ : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

def box₂ : Set ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioc (-π) π

def box : Set (F K) := (box₁ K) ×ˢ (box₂ K)

def normLessThanOnePlus : (Set (E K)) := (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}

theorem eval₀ :
    mapToUnitsPow K '' (box₁ K) = normVector K '' (normLessThanOnePlus K ) := sorry

theorem normLessThanOnePlus_eq_image :
    normLessThanOnePlus K  = full_marcus K '' (box K) := by
  unfold full_marcus box
  simp_rw [PartialHomeomorph.coe_trans, Set.image_comp, marcus₁_image_prod]
  rw [box₂, eval₀]
  convert (image_by_marcus₃ K (normLessThanOnePlus K) ?_ ?_).symm
  · sorry
  · sorry
  · sorry
  · sorry

-- open ENNReal in
-- private theorem volume_marcus₃_set_prod_set_aux
--     (f : (InfinitePlace K → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ) → ℝ≥0∞)
--     (W : Finset {w : InfinitePlace K // w.IsComplex}) (hf : Measurable f)
--     (a : {w : InfinitePlace K // w.IsComplex} → ℂ) (x : {w : InfinitePlace K // w.IsReal} → ℝ) :
--     (∫⋯∫⁻_W, fun y ↦ f ⟨x, fun w ↦ ‖y w‖⟩ ∂fun _ ↦ (volume : Measure ℂ)) a =
--       (2 * NNReal.pi) ^ W.card * (∫⋯∫⁻_W, (fun y ↦ (∏ i ∈ W, (y i).toNNReal) * f ⟨x, y⟩)
--         ∂fun _ ↦ (volume.restrict (Set.Ici (0 : ℝ)))) (fun i ↦ ‖a i‖) := by
--   sorry

-- example (s : Set (InfinitePlace K → ℝ)) (t : {w : InfinitePlace K // IsComplex w} → Set ℝ)
--     (W : Finset {w : InfinitePlace K // w.IsComplex}) (a : {w : InfinitePlace K // IsComplex w} → ℂ)
--     (x : {w : InfinitePlace K // IsReal w} → ℝ) :
--     (∫⋯∫⁻_W, fun y ↦ (s ×ˢ Set.univ.pi fun w ↦ t w).indicator 1 (x, y)
--       ∂fun _ ↦ (volume : Measure ℂ)) a = ∏ w ∈ W, volume (t w) * ∫⁻ a, s.indicator 1 a := sorry



-- Prove the full_marcus version below instead?
theorem volume_marcus₃_set_prod_set (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
   -- (t : {w : InfinitePlace K // IsComplex w} → Set ℝ) :
--    volume (marcus₃ K '' (s ×ˢ (Set.univ.pi fun w ↦ t w))) = ∏ w, volume (t w) *
    volume (marcus₃ K '' s ×ˢ t) = volume t *
      ∫⁻ x in s, ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator]
  rw [lintegral_marcus₃]
  simp_rw [Set.indicator_image sorry]
  rw [Measure.volume_eq_prod, lintegral_prod]
  simp_rw [show (fun _ ↦ (1 : ℝ≥0∞)) ∘ (marcus₃ K) = fun _ ↦ 1 by aesop]
  have : ∀ x y,
    (s ×ˢ t).indicator (fun x ↦ (1 : ℝ≥0∞)) (x, y) = (s.indicator 1 x) * (t.indicator 1 y) := by
      intro x y
      exact Set.indicator_prod_one
  simp_rw [this]
  simp_rw [lintegral_const_mul' _ _ sorry]
  simp_rw [lintegral_indicator _ sorry, Pi.one_apply, setLIntegral_one, ← mul_assoc]
  rw [lintegral_mul_const', mul_comm]
  rw [← lintegral_indicator]
  congr
  ext

  all_goals sorry

theorem volume_full_marcus_set_prod_set (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    volume (full_marcus K '' (s ×ˢ t)) =
    volume t * ∫⁻ x in mapToUnitsPow K '' s,
      ∏ w : { w : InfinitePlace K // w.IsComplex }, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator, Measure.volume_eq_prod, lintegral_prod]
  rw [full_marcus, PartialHomeomorph.coe_trans, Set.image_comp, marcus₁_image_prod]
  rw [marcus₃]
  simp only [PartialHomeomorph.coe_trans, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Homeomorph.toPartialHomeomorph_apply, Function.comp_apply,
    marcus₂_apply]
  all_goals sorry

def jacobianCoeff (w i : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
    fun c ↦ if hi : i = w₀ then 1 else (c w₀) * (w (fundSystem K (equivFinRank ⟨i, hi⟩))).log

def jacobian : (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) →L[ℝ] InfinitePlace K → ℝ := by
  intro c
  refine ContinuousLinearMap.pi ?_
  intro i
  exact (mapToUnitsPow₀ K (fun w ↦ c w) i •
    ∑ w, (jacobianCoeff K i w c) • ContinuousLinearMap.proj w)

theorem hasFDeriv_mapToUnitsPow (c : InfinitePlace K → ℝ) :
    HasFDerivAt (mapToUnitsPow K) (jacobian K c) c := sorry

-- Generalize!
theorem injOn_mapToUnitsPow :
    Set.InjOn (mapToUnitsPow K) (box₁ K) := by
  refine Set.InjOn.mono (Set.pi_mono fun _ _ ↦ ?_) (mapToUnitsPow K).injOn
  split_ifs
  exact Set.Ioc_subset_Ioi_self
  exact Set.subset_univ _

theorem jacobian_det (c : InfinitePlace K → ℝ) :
    |(jacobian K c).det| =
      (∏ w : {w : InfinitePlace K // w.IsComplex }, mapToUnitsPow K (fun w ↦ c w) w)⁻¹ *
        2⁻¹ ^ NrComplexPlaces K * |c w₀| ^ (rank K) * (finrank ℚ K) * regulator K := by
  sorry

-- theorem volume_normLessThanOnePlus :
--     (volume (normLessThanOnePlus K)).toReal = π ^ NrComplexPlaces K * regulator K := by
--   rw [normLessThanOnePlus_eq_image, box, volume_full_marcus_set_prod_set]
--   rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
--      (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
--      (injOn_mapToUnitsPow K)]
--   simp_rw [jacobian_det]
--   sorry

theorem lintegral_mapToUnitsPow (s : Set (InfinitePlace K → ℝ)) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s,
          (∏ i : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (mapToUnitsPow K x i))⁻¹ *
        ENNReal.ofReal |x w₀| ^ rank K * f (mapToUnitsPow K x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
     (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
     sorry]
  simp_rw [jacobian_det]
  rw [← lintegral_const_mul']
  congr with x
  rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow, ENNReal.ofReal_pow]
  rw [ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_prod_of_nonneg]
  ring_nf
  
  all_goals sorry

theorem closure_subset_closure :
    closure (normLessThanOnePlus K) ⊆ full_marcus K '' (closure (box K)) := by
  refine closure_minimal ?_ ?_
  · rw [normLessThanOnePlus_eq_image]
    refine Set.image_mono ?_
    exact subset_closure
  · have t₁ : IsCompact (closure (box K)) := sorry
    have t₂ : ContinuousOn (full_marcus K) (closure (box K)) := sorry
    have := t₁.image_of_continuousOn t₂
    exact IsCompact.isClosed this

theorem box_subset_source :
    (box K) ⊆ (full_marcus K).source := sorry

theorem normLessThanOnePlus_subset_target :
    normLessThanOnePlus K ⊆ (full_marcus K).target := sorry

theorem interior_eq_interior :
    full_marcus K '' (interior (box K)) = interior (normLessThanOnePlus K) := by
  have : (full_marcus K).IsImage (box K) (normLessThanOnePlus K) := sorry
  have := this.interior
  have := PartialHomeomorph.IsImage.image_eq this
  rwa [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr] at this
  · refine subset_trans ?_ (normLessThanOnePlus_subset_target K)
    exact interior_subset
  · refine subset_trans ?_ (box_subset_source K)
    exact interior_subset

example : volume (full_marcus K '' (interior (box K))) =
    volume (full_marcus K '' (closure (box K))) := by
  have : interior (box K) =
    (Set.univ.pi fun _ ↦ Set.Ioo 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := sorry
  rw [this]
  clear this
  have : closure (box K) = (Set.Icc 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Icc (-π) π) := sorry
  rw [this]
  clear this
  rw [volume_full_marcus_set_prod_set, volume_full_marcus_set_prod_set]
  congr 1
  · simp_rw [volume_pi_pi, Real.volume_Ioo, Real.volume_Icc]
  · rw [lintegral_mapToUnitsPow, lintegral_mapToUnitsPow]
    congr 1
    refine setLIntegral_congr ?_
    rw [show (Set.univ.pi fun _ ↦ Set.Ioo (0 : ℝ) 1) = interior (Set.Icc 0 1) by
      simp_rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ, Pi.zero_apply, Pi.one_apply,
        interior_Icc]]
    exact interior_ae_eq_of_null_frontier ((convex_Icc _ _).addHaar_frontier volume)
