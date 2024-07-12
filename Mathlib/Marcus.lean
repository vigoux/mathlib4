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

local notation "F" K => (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

@[simps source target]
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

def box₁ : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

def box₂ : Set ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioc (-π) π

def box : Set (F K) := (box₁ K) ×ˢ (box₂ K)

def normLessThanOnePlus : (Set (E K)) := (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}

theorem eval₀ :
    mapToUnitsPow K '' (box₁ K) = normVector K '' (normLessThanOnePlus K ) := sorry

theorem eval :
    full_marcus K '' (box K) = normLessThanOnePlus K := by
  unfold full_marcus box
  simp_rw [PartialHomeomorph.coe_trans, Set.image_comp, marcus₁_image_prod]
  rw [box₂, eval₀]
  convert (image_by_marcus₃ K (normLessThanOnePlus K) ?_ ?_).symm
  · sorry
  · sorry

theorem volume_marcus₃_prod_box₂ (s : Set (InfinitePlace K → ℝ)) :
    volume (marcus₃ K '' (s ×ˢ box₂ K)) = (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ x in s, ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal:= by
  sorry

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

theorem volume_normLessThanOnePlus :
    (volume (normLessThanOnePlus K)).toReal = π ^ NrComplexPlaces K * regulator K := by
  simp_rw [← eval, full_marcus, PartialHomeomorph.coe_trans, box]
  simp_rw [Set.image_comp, marcus₁_image_prod]
  rw [volume_marcus₃_prod_box₂]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
     (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
     (injOn_mapToUnitsPow K)]
  simp_rw [jacobian_det]
  sorry
