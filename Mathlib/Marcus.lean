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

def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def realToMixed : (InfinitePlace K → ℝ) →ₐ[ℝ] (E K) := AlgHom.prod
    (Pi.algHom fun w ↦ Pi.evalAlgHom _ _ w.val)
    (Pi.algHom fun w ↦ Complex.ofRealAm.comp  <| Pi.evalAlgHom _ _ w.val)

@[simp]
theorem normAtPlace_realToMixed (w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    normAtPlace w (realToMixed x) = |x w| := by
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtPlace_apply_isReal hw, realToMixed]
  · simp [normAtPlace_apply_isComplex hw, realToMixed]

@[simp]
theorem norm_realToMixed (x : InfinitePlace K → ℝ) :
    mixedEmbedding.norm (realToMixed x) = ∏ w, |x w| ^ w.mult :=
  Finset.prod_congr rfl fun w _ ↦ by simp

variable (K)

-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀_aux :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c w ↦ if hw : w = w₀ then
      Real.exp (- ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ * ∑ w : {w // w ≠ w₀}, c w)
    else Real.exp ((w.mult : ℝ)⁻¹ * c ⟨w, hw⟩)
  invFun := fun x w ↦ w.val.mult * Real.log (x w.val)
  source := Set.univ
  target := {x | ∀ w, 0 < x w} ∩ {x | ∑ w, w.mult * Real.log (x w) = 0}
  map_source' _ _ := by
    dsimp only
    refine ⟨Set.mem_setOf.mpr fun w ↦ by split_ifs <;> exact Real.exp_pos _, ?_⟩
    rw [Set.mem_setOf_eq, ← Finset.univ.sum_erase_add _ (Finset.mem_univ w₀), dif_pos rfl]
    rw [Finset.sum_subtype _ (by aesop : ∀ w, w ∈ Finset.univ.erase w₀ ↔ w ≠ w₀)]
    conv_lhs => enter [1,2,w]; rw [dif_neg w.prop]
    simp_rw [Real.log_exp, neg_mul, mul_neg, mul_inv_cancel_left₀ mult_coe_ne_zero,
      add_neg_eq_zero]
    infer_instance
  map_target' _ _ := trivial
  left_inv' := by
    intro x _
    dsimp only
    ext w
    rw [dif_neg w.prop, Real.log_exp,  mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' := by
    intro x hx
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, ← Finset.sum_subtype _
        (by aesop : ∀ w, w ∈ Finset.univ.erase w₀ ↔ w ≠ w₀) (fun w ↦ w.mult * Real.log (x w))]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ w₀), hx.2, _root_.zero_sub, neg_mul, mul_neg,
        neg_neg, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w₀)]
    · rw [dif_neg hw, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w)]

theorem continuous_mapToUnitsPow₀_aux :
    Continuous (mapToUnitsPow₀_aux K) := by
  unfold mapToUnitsPow₀_aux
  refine continuous_pi_iff.mpr fun w ↦ ?_
  by_cases hw : w = w₀
  · simp_rw [dif_pos hw]
    fun_prop
  · simp_rw [dif_neg hw]
    fun_prop

theorem continuousOn_mapToUnitsPow₀_aux_symm :
    ContinuousOn (mapToUnitsPow₀_aux K).symm {x | ∀ w, x w ≠ 0} :=
  continuousOn_pi.mpr fun w ↦
    continuousOn_const.mul <| (continuousOn_apply _ _).log fun _ h ↦ h w

-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀ :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (InfinitePlace K → ℝ) :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
    equivFinRank).equivFun.symm.toEquiv.toPartialEquiv.trans (mapToUnitsPow₀_aux K)

theorem mapToUnitsPow₀_source :
    (mapToUnitsPow₀ K).source = Set.univ := by simp [mapToUnitsPow₀, mapToUnitsPow₀_aux]

theorem mapToUnitsPow₀_target :
    (mapToUnitsPow₀ K).target = {x | (∀ w, 0 < x w) ∧ mixedEmbedding.norm (realToMixed x) = 1} := by
  rw [mapToUnitsPow₀, mapToUnitsPow₀_aux]
  dsimp
  ext x
  simp_rw [Set.inter_univ, Set.mem_inter_iff, Set.mem_setOf, and_congr_right_iff]
  intro hx
  rw [← Real.exp_injective.eq_iff, Real.exp_zero, Real.exp_sum, norm_realToMixed]
  refine Eq.congr (Finset.prod_congr rfl fun _ _ ↦ ?_) rfl
  rw [← Real.log_rpow (hx _), Real.exp_log (Real.rpow_pos_of_pos (hx _) _), abs_of_pos (hx _),
    Real.rpow_natCast]

theorem norm_mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realToMixed (mapToUnitsPow₀ K c)) = 1 := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.2
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.1 w
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = fun w ↦ ∏ i, w.val (fundSystem K (equivFinRank.symm i)) ^ (c i) := by
  ext w
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply,
    LinearEquiv.coe_toEquiv, mapToUnitsPow₀_aux, Function.comp_apply, Basis.equivFun_symm_apply,
    Basis.coe_reindex, Function.comp_apply, Basis.ofZlatticeBasis_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, neg_mul, ← logEmbedding_fundSystem, Finset.mul_sum]
  by_cases hw : w = w₀
  · rw [dif_pos hw, Finset.sum_comm, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp_rw [← Finset.mul_sum, sum_logEmbedding_component, ← mul_assoc, mul_comm _ (c _),
      mul_assoc (c _), hw, mul_neg, neg_mul, mul_neg, neg_neg, inv_mul_cancel mult_coe_ne_zero,
      one_mul]
    conv_lhs =>
      enter [2, i]
      rw [← Real.log_rpow (pos_iff.mpr (by simp))]
    conv_lhs =>
      enter [2, i]
      rw [Real.exp_log (by exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]
    rfl
  · rw [dif_neg hw, Real.exp_sum]
    congr with x
    rw [logEmbedding_component, ← mul_assoc, ← mul_assoc, mul_comm _ (c _), mul_assoc (c _),
      inv_mul_cancel mult_coe_ne_zero, mul_one, ← Real.log_rpow (pos_iff.mpr (by simp)),
      Real.exp_log (Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]
    rfl

-- theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
--     (hx : mixedEmbedding.norm (realToMixed x) = 1) :
--     (mapToUnitsPow₀_aux K).symm x = logMap (realToMixed x) := by
--   ext w
--   rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
--     normAtPlace_realToMixed, Real.log_abs]

theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀ K).symm x = (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
      equivFinRank).equivFun (logMap (realToMixed x)) := by
  rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm,  EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.log_abs]

theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ K) := (continuous_mapToUnitsPow₀_aux K).comp <|
  LinearEquiv.continuous_symm _ (continuous_equivFun_basis _)

theorem continuousOn_mapToUnitsPow₀_symm :
    ContinuousOn (mapToUnitsPow₀ K).symm {x | ∀ w, x w ≠ 0} :=
  (continuous_equivFun_basis _).comp_continuousOn (continuousOn_mapToUnitsPow₀_aux_symm K)

def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w)
  invFun := by
    intro x w
    by_cases hw : w = w₀
    · exact mixedEmbedding.norm (realToMixed x) ^ (finrank ℚ K : ℝ)⁻¹
    · exact (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
        equivFinRank).equivFun (logMap (realToMixed x)) ⟨w, hw⟩
  source := Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ
  target := Set.univ.pi fun _ ↦ Set.Ioi 0
  map_source' := sorry
  map_target' := sorry
  left_inv' := by
    intro x hx
    rw [_root_.map_smul, logMap_smul]
    · ext w
      by_cases hw : w = w₀
      · rw [hw, dif_pos rfl, mixedEmbedding.norm_smul, norm_mapToUnitsPow₀, mul_one]
        sorry
      · rw [dif_neg hw, ← mapToUnitsPow₀_symm_apply K (norm_mapToUnitsPow₀ K _),
          PartialEquiv.left_inv _ (by rw [mapToUnitsPow₀_source]; trivial )]
    · rw [norm_mapToUnitsPow₀]
      exact one_ne_zero
    · have := (if_pos rfl) ▸ Set.mem_univ_pi.mp hx w₀
      exact abs_ne_zero.mpr (ne_of_gt (by exact this))
  right_inv' := by
    intro x hx
    ext w
    dsimp only
    rw [dif_pos rfl]
    simp_rw [dif_neg sorry]
    rw [← mapToUnitsPow₀_symm_apply, PartialEquiv.right_inv, Pi.smul_apply, smul_eq_mul,
      norm_realToMixed]
    
#exit
    by_cases hw : w = w₀
    · dsimp only

      sorry
    · dsimp only

      sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry


#exit

def expMap₀_aux : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
    (InfinitePlace K → ℝ) where
  toFun x w := if hw : w = w₀ then
      Real.exp (- ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ * ∑ w : {w // w ≠ w₀}, x w)
      else Real.exp ((w.mult : ℝ)⁻¹ * x ⟨w, hw⟩)
  invFun x w := w.val.mult * Real.log (x w)
  source := Set.univ
  target := (Set.univ.pi fun _ ↦ Set.Ioi 0) ∩
    {x | - ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ *
      ∑ w : { w // w ≠ w₀ }, w.val.mult * Real.log (x w.val) = Real.log (x w₀)}
  map_source' _ _ := by
    dsimp only
    refine ⟨?_, ?_⟩
    · refine Set.mem_univ_pi.mpr fun _ ↦ ?_
      split_ifs <;> exact Real.exp_pos _
    · rw [Set.mem_setOf_eq, dif_pos rfl]
      conv_lhs =>
        enter [2, 2, w]
        rw [dif_neg w.prop]
      simp_rw [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  map_target' _ _ := trivial
  left_inv' _ _ := by
    ext w
    simp_rw [dif_neg w.prop, Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' x hx := by
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, hx.2, Real.exp_log ((Set.mem_univ_pi.mp hx.1) _)]
    · rw [dif_neg hw, inv_mul_cancel_left₀ mult_coe_ne_zero,
        Real.exp_log ((Set.mem_univ_pi.mp hx.1) _)]
  open_source := isOpen_univ
  open_target := by
      dsimp only
      refine IsOpen.inter ?_ ?_
      · sorry
      · refine
        IsLocallyInjective.isOpen_eqLocus ?refine_2.inj ?refine_2.h₁ ?refine_2.h₂ ?refine_2.he
        sorry
--      refine isOpen_set_pi Set.finite_univ ?_

    -- isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
  continuousOn_toFun := by
      sorry
  --  continuousOn_pi'
  --    fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i _)).rexp
  continuousOn_invFun := by
      sorry
  -- continuousOn_pi' fun i ↦ ContinuousOn.mul continuousOn_const <|
  --  (continuousOn_apply i _).log <| fun _ h ↦ ne_of_gt <| (Set.mem_univ_pi.mp h) i

#exit

def expMap₀ : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
    (InfinitePlace K → ℝ) := PartialHomeomorph.trans
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
    equivFinRank).equivFunL.symm.toHomeomorph.toPartialHomeomorph (expMap₀_aux K)

theorem expMap₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    expMap₀ K c = fun w ↦ ∏ i, w.val (fundSystem K (equivFinRank.symm i)) ^ (c i) := by
  ext w
  erw [expMap₀, PartialHomeomorph.coe_trans, Homeomorph.toPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, Basis.equivFun_symm_apply]
  simp_rw [Basis.coe_reindex, Function.comp_apply, Basis.ofZlatticeBasis_apply, expMap₀_aux,
    PartialHomeomorph.mk_coe, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← logEmbedding_fundSystem]
  by_cases hw : w = w₀
  · rw [dif_pos hw, Finset.sum_comm, Real.exp_sum]
    simp_rw [← Finset.mul_sum, sum_logEmbedding_component, ← mul_assoc, mul_comm _ (c _),
      mul_assoc (c _), hw, mul_neg, neg_mul, neg_neg, inv_mul_cancel mult_coe_ne_zero, one_mul]
    conv_lhs =>
      enter [2, i]
      rw [← Real.log_rpow (pos_iff.mpr (by simp))]
    conv_lhs =>
      enter [2, i]
      rw [Real.exp_log (by exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]
    rfl
  · rw [dif_neg hw, Real.exp_sum]
    congr with x
    rw [logEmbedding_component, ← mul_assoc, ← mul_assoc, mul_comm _ (c _), mul_assoc (c _),
      inv_mul_cancel mult_coe_ne_zero, mul_one, ← Real.log_rpow (pos_iff.mpr (by simp)),
      Real.exp_log (Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]
    rfl


#exit

def expMap₀_aux : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
  toFun := fun x w ↦ Real.exp ((w.val.mult : ℝ)⁻¹ * x w)
  invFun := fun x w ↦ w.val.mult * Real.log (x w)
  source := Set.univ
  target := Set.univ.pi fun _ ↦ Set.Ioi 0
  map_source' _ _ := Set.mem_univ_pi.mpr fun _ ↦ Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by ext; simp
  right_inv' _ h := by ext; simpa using Real.exp_log <| (Set.mem_univ_pi.mp h) _
  open_source := isOpen_univ
  open_target := isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
  continuousOn_toFun := continuousOn_pi'
    fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i _)).rexp
  continuousOn_invFun := continuousOn_pi' fun i ↦ ContinuousOn.mul continuousOn_const <|
    (continuousOn_apply i _).log <| fun _ h ↦ ne_of_gt <| (Set.mem_univ_pi.mp h) i

def expMap₀ : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) := PartialHomeomorph.trans
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
    equivFinRank).equivFunL.symm.toHomeomorph.toPartialHomeomorph (expMap₀_aux K)

theorem expMap₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    expMap₀ K c = fun w ↦ ∏ i, w.val (fundSystem K (equivFinRank.symm i)) ^ (c i) := by
  ext w
  erw [expMap₀, PartialHomeomorph.coe_trans, Homeomorph.toPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, Basis.equivFun_symm_apply]
  simp_rw [Basis.coe_reindex, Function.comp_apply, Basis.ofZlatticeBasis_apply, expMap₀_aux,
    PartialHomeomorph.mk_coe, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Real.exp_sum, ← logEmbedding_fundSystem, logEmbedding_component]
  congr with x
  rw [← mul_assoc, ← mul_assoc, mul_comm _ (c _), mul_assoc (c _), inv_mul_cancel
      (by rw [Nat.cast_ne_zero]; exact mult_ne_zero), mul_one, ← Real.log_rpow
      (pos_iff.mpr (by simp)), Real.exp_log (Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]

def expMap_aux : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := by
    intro x w
    by_cases hw : w = w₀
    · exact (x w₀) * (∏ w ∈ Finset.univ.erase w₀, x w)⁻¹
    · exact (x w₀) * x w
  invFun := by
    intro x w
    let x₀ := (∏ w, (x w)) ^ (Fintype.card (InfinitePlace K) : ℝ)⁻¹
    by_cases hw : w = w₀
    · exact x₀
    · exact x₀⁻¹ * (x w)
  source := sorry
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := by
    intro x _
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, ← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), dif_pos rfl]
      sorry
    · simp_rw [dif_neg hw]
      sorry
  right_inv' := by
    intro x _
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [dif_pos hw, dif_pos rfl]
      sorry
    · rw [dif_neg hw, dif_neg hw, dif_pos rfl, ← mul_assoc, mul_inv_cancel, one_mul]
      sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

def expMap : (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) := by
  intro c
  let u := expMap₀ K (fun w ↦ c w.val)
  exact expMap_aux K
    (fun w ↦ if hw : w = w₀ then c w₀ else u ⟨w, hw⟩)

theorem expMap_apply (c : InfinitePlace K → ℝ) :
    expMap K c = fun w ↦ (c w₀) • ∏ i, w.val (fundSystem K (equivFinRank.symm i)) ^ (c i.val) := by
  ext w
  by_cases hw : w = w₀
  · sorry
  · sorry


#exit

def expMap : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := by
    intro c



#exit

-- def expMap₀ : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
--     ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
--   toFun := fun x w ↦ rexp (mult w.val * x w)
--   invFun := fun x w ↦ (mult w.val : ℝ)⁻¹ * Real.log (x w)
--   source := Set.univ
--   target := Set.univ.pi fun _ ↦ Set.Ioi 0
--   map_source' _ _ := Set.mem_univ_pi.mpr fun _ ↦ Real.exp_pos _
--   map_target' _ _ := trivial
--   left_inv' _ := by simp
--   right_inv' _ h := by simpa using funext fun _ ↦ by rw [Real.exp_log (h _ trivial)]
--   open_source := isOpen_univ
--   open_target := isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
--   continuousOn_toFun := continuousOn_pi'
--     fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i _)).rexp
--   continuousOn_invFun := continuousOn_pi' fun i ↦ ContinuousOn.mul continuousOn_const <|
--     (continuousOn_apply i _).log <| fun _ h ↦ ne_of_gt <| (Set.mem_univ_pi.mp h) i

def mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ (c i)

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := sorry

theorem prod_mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w, (mapToUnitsPow₀ K c w) ^ mult w = 1 := sorry

def realToMixed : (InfinitePlace K → ℝ) →ₐ[ℝ] (E K) := AlgHom.prod
    (Pi.algHom fun w ↦ Pi.evalAlgHom _ _ w.val)
    (Pi.algHom fun w ↦ Complex.ofRealAm.comp  <| Pi.evalAlgHom _ _ w.val)

def logRepr (x : InfinitePlace K → ℝ) : ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex equivFinRank).repr (logMap (realToMixed K x))

theorem logRepr_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {x : ι → (InfinitePlace K → ℝ)}
    (hx : ∀ i ∈ s, mixedEmbedding.norm (realToMixed K (x i)) ≠ 0) :
    logRepr K (∏ i ∈ s, x i) = ∑ i ∈ s, logRepr K (x i) := by
  rw [logRepr, map_prod, logMap_prod s hx, _root_.map_sum, Finsupp.coe_finset_sum]
  rfl

theorem logRepr_unit_rpow (u : (𝓞 K)ˣ) (c : ℝ) :
    logRepr K (fun w ↦ (w u) ^ c) = c • logEmbedding K u := by
  sorry

theorem logRepr_mapToUnitPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    logRepr K (mapToUnitsPow₀ K c) = c := by
  unfold mapToUnitsPow₀
  rw [← Finset.prod_fn, logRepr_prod]


#exit
  have : (fun w : InfinitePlace K ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ (c i)) =
      ∏ i, fun w : InfinitePlace K ↦ w (fundSystem K (equivFinRank.symm i)) ^ (c i) := by
    exact
      Eq.symm
        (prod_fn univ fun c_1 w ↦
          w ((algebraMap (𝓞 K) K) ↑(fundSystem K (equivFinRank.symm c_1))) ^ c c_1)
  sorry

-- Refactor this definition
@[simps apply source target]
def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w)
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

theorem prod_mapToUnitsPow (c : InfinitePlace K → ℝ) :
    ∏ w, (mapToUnitsPow K c w) ^ mult w = (c w₀) ^ mult (w₀ : InfinitePlace K) := sorry

theorem mapToUnitsPow_nonneg (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 ≤ mapToUnitsPow K c w  := by
  rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul]
  refine mul_nonneg ?_ ?_
  · sorry -- exact Real.rpow_nonneg (abs_nonneg _) _
  · exact (mapToUnitsPow₀_pos _ _ _).le

theorem mapToUnitsPow_zero_iff (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    mapToUnitsPow K c w = 0 ↔ c w₀ = 0 := by
  sorry
  -- simp_rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
  --   ne_of_gt (mapToUnitsPow₀_pos _ _ _), or_false, Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _),
  --   abs_eq_zero, and_iff_left_iff_imp, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ← ne_eq]
  -- intro _
  -- exact ne_of_gt finrank_pos

abbrev mapToUnitsPow_single (c : (InfinitePlace K → ℝ)) : InfinitePlace K → (InfinitePlace K → ℝ) :=
  fun i ↦ if hi : i = w₀ then fun _ ↦ |c w₀| else
    fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (c i)

theorem mapToUnitsPow₀_eq_prod_single (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    mapToUnitsPow₀ K (fun w ↦ c w.val) w =
      ∏ i ∈ univ.erase w₀, mapToUnitsPow_single K c i w := by
  rw [mapToUnitsPow₀, Finset.prod_subtype (Finset.univ.erase w₀)
    (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
  conv_rhs =>
    enter [2, i]
    rw [mapToUnitsPow_single, dif_neg i.prop]

theorem mapToUnitsPow_eq_prod_single (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    mapToUnitsPow K c w = ∏ i, mapToUnitsPow_single K c i w := by
  rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), mapToUnitsPow_apply, Pi.smul_apply,
    mapToUnitsPow₀_eq_prod_single, smul_eq_mul, mapToUnitsPow_single, dif_pos rfl]

open ContinuousLinearMap

abbrev mapToUnitsPow_fDeriv_single (c : InfinitePlace K → ℝ) (i w : InfinitePlace K) :
    (InfinitePlace K → ℝ) →L[ℝ] ℝ := by
  exact if hi : i = w₀ then proj w₀ else
    (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)) ^ c i *
      (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log) • proj i

theorem mapToUnitsPow_hasFDeriv_single (c : InfinitePlace K → ℝ) (i w : InfinitePlace K)
    (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (fun x ↦ mapToUnitsPow_single K x i w)
      (mapToUnitsPow_fDeriv_single K c i w) {x | 0 ≤ x w₀} c := by
  unfold mapToUnitsPow_single mapToUnitsPow_fDeriv_single
  split_ifs
  · refine HasFDerivWithinAt.congr' (hasFDerivWithinAt_apply w₀ c _) ?_ hc
    exact fun _ h ↦ by simp_rw [abs_of_nonneg (Set.mem_setOf.mp h)]
  · exact HasFDerivWithinAt.const_rpow (hasFDerivWithinAt_apply i c _) <| pos_iff.mpr (by aesop)

abbrev jacobianCoeff (w i : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
  fun c ↦ if hi : i = w₀ then 1 else |c w₀| * (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log

abbrev jacobian (c : InfinitePlace K → ℝ) : (InfinitePlace K → ℝ) →L[ℝ] InfinitePlace K → ℝ :=
  pi fun i ↦ (mapToUnitsPow₀ K (fun w ↦ c w) i • ∑ w, (jacobianCoeff K i w c) • proj w)

theorem mapToUnitsPow_hasFDeriv (c : InfinitePlace K → ℝ) (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (mapToUnitsPow K) (jacobian K c) {x | 0 ≤ x w₀} c := by
  refine hasFDerivWithinAt_pi'.mpr fun w ↦ ?_
  simp_rw [mapToUnitsPow_eq_prod_single]
  convert HasFDerivWithinAt.finset_prod fun i _ ↦ mapToUnitsPow_hasFDeriv_single K c i w hc
  rw [ContinuousLinearMap.proj_pi, Finset.smul_sum]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  by_cases hi : i = w₀
  · simp_rw [hi, jacobianCoeff, dite_true, one_smul, dif_pos, mapToUnitsPow₀_eq_prod_single]
  · rw [mapToUnitsPow₀_eq_prod_single, jacobianCoeff, dif_neg hi, smul_smul, ← mul_assoc,
      show |c w₀| = mapToUnitsPow_single K c w₀ w by simp_rw [dif_pos rfl], Finset.prod_erase_mul _ _
      (Finset.mem_univ w₀), mapToUnitsPow_fDeriv_single, dif_neg hi, smul_smul,  ← mul_assoc,
      show w (algebraMap (𝓞 K) K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ c i =
        mapToUnitsPow_single K c i w by simp_rw [dif_neg hi], Finset.prod_erase_mul _ _
        (Finset.mem_univ i)]









#exit

  simp only [mapToUnitsPow_apply, ne_eq, Pi.smul_apply, smul_eq_mul]
  simp only [mapToUnitsPow₀]
  let A : (InfinitePlace K → ℝ) → InfinitePlace K → (InfinitePlace K → ℝ) :=
    fun x i ↦ if hi : i = w₀ then fun _ ↦ |x w₀| else
      fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (x i)
  convert_to HasFDerivAt
    (fun x ↦ ∏ i, A x i w) ((ContinuousLinearMap.proj w).comp (jacobian K c)) c
  · ext x
    rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀)]
    congr!
    · simp [A]
    · dsimp only [A]
      rw [Finset.prod_subtype (Finset.univ.erase w₀)
        (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [dif_neg]






#exit
  let p : InfinitePlace K → ((InfinitePlace K → ℝ) →L[ℝ] ℝ) :=
    fun i ↦ if hi : i = w₀ then ContinuousLinearMap.proj w₀ else
      (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)) ^ (c i) *
        (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log) • ContinuousLinearMap.proj i

  have := HasFDerivAt.finset_prod (fun i _ ↦ p i)
  simp [jacobian]
  dsimp only
--  have : HasFDerivAt (fun x ↦ |x w₀| ^ (finrank ℚ K : ℝ)⁻¹)
--  refine HasFDerivAt.mul ?_ ?_


#exit


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



local notation "F" K => (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

-- def expMap₀ : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
--     ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
--   toFun := fun x w ↦ rexp (mult w.val * x w)
--   invFun := fun x w ↦ (mult w.val : ℝ)⁻¹ * Real.log (x w)
--   source := Set.univ
--   target := Set.univ.pi fun _ ↦ Set.Ioi 0
--   map_source' _ _ := Set.mem_univ_pi.mpr fun _ ↦ Real.exp_pos _
--   map_target' _ _ := trivial
--   left_inv' _ := by simp
--   right_inv' _ h := by simpa using funext fun _ ↦ by rw [Real.exp_log (h _ trivial)]
--   open_source := isOpen_univ
--   open_target := isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
--   continuousOn_toFun := continuousOn_pi'
--     fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i _)).rexp
--   continuousOn_invFun := continuousOn_pi' fun i ↦ ContinuousOn.mul continuousOn_const <|
--     (continuousOn_apply i _).log <| fun _ h ↦ ne_of_gt <| (Set.mem_univ_pi.mp h) i

-- def expMap : PartialHomeomorph ({w : InfinitePlace K // w ≠ w₀} → ℝ)
--     ({w : InfinitePlace K // w ≠ w₀} → ℝ) := PartialHomeomorph.trans
--   (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex equivFinRank.symm).equivFunL.toHomeomorph.toPartialHomeomorph
--   (expMap₀ K)

-- def expMapFull : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
--   toFun := by
--     intro x
--     let y := expMap K (fun w ↦ x w.val)
--     intro w
--     by_cases hw : w = w₀
--     · exact (x w₀) * (∏ w, y w)⁻¹
--     · exact (x w₀) * (y ⟨w, hw⟩)
--   invFun := by
--     intro x w
--     let P := ∏ w, x w
--     by_cases hw : w = w₀
--     · exact P
--     · exact
--       sorry


-- -- Refactor this definition
-- @[simps apply source target]
-- def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
--   toFun := fun c ↦ |c w₀| ^ (finrank ℚ K : ℝ)⁻¹ • mapToUnitsPow₀ K (fun w ↦ c w)
--   invFun := sorry
--   source := Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ
--   target := Set.univ.pi fun _ ↦ Set.Ioi 0
--   map_source' := sorry
--   map_target' := sorry
--   left_inv' := sorry
--   right_inv' := sorry
--   open_source := sorry
--   open_target := sorry
--   continuousOn_toFun := sorry
--   continuousOn_invFun := sorry



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
          ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w}, (mapToUnitsPow K x i))⁻¹ *
        ENNReal.ofReal |x w₀| ^ rank K * f (mapToUnitsPow K x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
     (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
     sorry]
  simp_rw [jacobian_det]
  rw [← lintegral_const_mul']
  congr with x
  rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow, ENNReal.ofReal_pow]
  rw [ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  ring_nf
  · positivity
  · positivity
  · rw [inv_nonneg]
    exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
  · refine mul_nonneg ?_ ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
    · positivity
  · refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
    · positivity
    · positivity
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
    · refine ENNReal.pow_ne_top ?_
      rw [ENNReal.inv_ne_top]
      exact two_ne_zero
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.natCast_ne_top _

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
