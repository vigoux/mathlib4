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

def marcus₁ : PartialHomeomorph (F K) (F K) :=
  PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _)

@[simp]
theorem marcus₁_apply (x : F K) : marcus₁ K x = (mapToUnitsPow K x.1, x.2) := rfl

@[simp]
theorem marcus₁_source : (marcus₁ K).source = (mapToUnitsPow K).source ×ˢ Set.univ := rfl

@[simp]
theorem marcus₂_target : (marcus₁ K).target = (mapToUnitsPow K).target ×ˢ Set.univ := rfl

local notation "G" K => ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

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

@[simp]
theorem marcus₂_apply (x : F K) :
    marcus₂ K x = (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩) := rfl

def marcus₃ : PartialHomeomorph (F K) (E K) :=
  (marcus₂ K).toPartialHomeomorph.trans <|
    (PartialHomeomorph.refl _).prod <| PartialHomeomorph.pi fun _ ↦ Complex.polarCoord.symm

theorem marcus₃_apply (x : F K) :
    marcus₃ K x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ x.1 w.val * (Real.cos (x.2 w) + Real.sin (x.2 w) * Complex.I)⟩ := by
  simp only [marcus₃, PartialHomeomorph.coe_trans, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Homeomorph.toPartialHomeomorph_apply, Function.comp_apply,
    marcus₂_apply, Complex.polarCoord_symm_apply]
  refine Prod.mk_inj_left.mpr ?_
  rw [PartialHomeomorph.pi]
  simp
  

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
    simp [PartialHomeomorph.pi, Complex.polardCoord_symm_abs]
    sorry

example : (marcus₃ K).source = {0} := by
  rw [marcus₃]
  rw [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.prod_toPartialEquiv,
    PartialHomeomorph.refl_partialEquiv, PartialHomeomorph.pi_toPartialEquiv,
    PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source]
  rw [Homeomorph.toPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    Homeomorph.toPartialHomeomorph_apply, PartialEquiv.prod_source, PartialEquiv.refl_source]
  rw [PartialEquiv.pi_source, PartialEquiv.symm_source, Set.univ_inter]
  rw [marcus₂]
  simp


  simp only [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.prod_toPartialEquiv,
    PartialHomeomorph.refl_partialEquiv, PartialHomeomorph.pi_toPartialEquiv,
    PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
    Homeomorph.toPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    Homeomorph.toPartialHomeomorph_apply, PartialEquiv.prod_source, PartialEquiv.refl_source,
    PartialEquiv.pi_source, PartialEquiv.symm_source, Set.univ_inter, Set.preimage_eq_univ_iff,
    Homeomorph.range_coe, Set.univ_subset_iff, Set.prod_eq_univ, true_and]
