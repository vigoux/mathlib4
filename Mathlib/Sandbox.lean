import Mathlib.Analysis.BoxIntegral.Integrability

noncomputable section

open MeasureTheory Submodule Filter Fintype

open scoped Pointwise NNReal ENNReal

variable (ι : Type*) (n : ℕ+)

def UnitBox : BoxIntegral.Box ι where
  lower := fun _ ↦ 0
  upper := fun _ ↦ 1
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBox_mem (x : ι → ℝ) : x ∈ UnitBox ι ↔ ∀ i, 0 < x i ∧ x i ≤ 1 := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBox, Set.mem_Ioc]

def UnitBoxPart (ν : ι → ℤ) : BoxIntegral.Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ ν i / n + 1 / n
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBoxPart_mem {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ UnitBoxPart ι n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxPart, Set.mem_Ioc]

def UnitBoxIndex (x : ι → ℝ) : ι → ℤ := fun i ↦ Int.ceil (n * x i) - 1

theorem UnitBoxIndex_apply {x : ι → ℝ} (i : ι) :
    UnitBoxIndex ι n x i = Int.ceil (n * (x : ι → ℝ) i) - 1 := rfl

theorem UnitBoxPart_mem_iff_index_eq {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ UnitBoxPart ι n ν ↔ UnitBoxIndex ι n x = ν := by
  rw [UnitBoxPart_mem]
  rw [Function.funext_iff]
  have h_npos : 0 < (n:ℝ) := by
    rw [Nat.cast_pos]
    exact PNat.pos n
  simp_rw [UnitBoxIndex_apply ι n, sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

-- Upper right corner
def UnitBoxTag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

theorem UnitBoxTag_mem_unitBoxPart (ν : ι → ℤ) :
    UnitBoxTag ι n ν ∈ UnitBoxPart ι n ν := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxTag, UnitBoxPart, Set.mem_Ioc]
  intro _
  refine ⟨?_, by rw [← add_div]⟩
  rw [div_lt_div_right <| Nat.cast_pos.mpr (PNat.pos n)]
  linarith

@[simp]
theorem UnitBoxIndex_tag (ν : ι → ℤ) :
    UnitBoxIndex ι n (UnitBoxTag ι n ν) = ν := by
  rw [← UnitBoxPart_mem_iff_index_eq]
  exact UnitBoxTag_mem_unitBoxPart _ _ _

theorem UnitBoxTag_injective : Function.Injective (UnitBoxTag ι n) := by
  intro _ _ h
  ext i
  have := congr_arg (fun x ↦ x i) h
  dsimp [UnitBoxTag] at this
  field_simp at this
  exact this

theorem UnitBoxPart_disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (UnitBoxPart ι n ν).toSet (UnitBoxPart ι n ν').toSet := by
  rw [not_iff_not.symm, ne_eq, not_not, Set.not_disjoint_iff]
  simp_rw [BoxIntegral.Box.mem_coe]
  refine ⟨?_, ?_⟩
  · intro h
    exact ⟨UnitBoxTag ι n ν, UnitBoxTag_mem_unitBoxPart ι n ν, h ▸ UnitBoxTag_mem_unitBoxPart ι n ν⟩
  · rintro ⟨x, hx, hx'⟩
    rw [UnitBoxPart_mem_iff_index_eq] at hx
    rw [UnitBoxPart_mem_iff_index_eq] at hx'
    rw [← hx, ← hx']

theorem UnitBoxPart_injective : Function.Injective (UnitBoxPart ι n) := by
  intro _ _ h
  contrapose! h
  rw [UnitBoxPart_disjoint] at h
  exact BoxIntegral.Box.ne_of_disjoint_coe h

variable [Fintype ι] [DecidableEq ι]

theorem UnitBoxPart_diam (ν : ι → ℤ) :
    Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) ≤ 1 / n := by
  rw [Metric.diam]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine EMetric.diam_pi_le_of_le ?_
  intro i
  rw [Real.ediam_Icc, UnitBoxPart]
  rw [add_sub_cancel', ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one]
  exact Nat.cast_pos.mpr n.pos

theorem UnitBoxPart_volume (ν : ι → ℤ) :
    (volume (UnitBoxPart ι n ν : Set (ι → ℝ))).toReal = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc]
  simp_rw [UnitBoxPart, add_sub_cancel']
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos, ENNReal.toReal_pow, ENNReal.toReal_div,
    div_pow, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, one_pow, Fintype.card]
  any_goals positivity
  exact Nat.cast_pos.mpr n.pos

def AdmissibleIndex :
  Finset (ι → ℤ) := Fintype.piFinset (fun _ ↦ Finset.Ico 0 (n:ℤ))

variable {ι n} in
theorem UnitBox_mem_iff_index {x : ι → ℝ} :
    x ∈ UnitBox ι ↔ UnitBoxIndex ι n x ∈ AdmissibleIndex ι n := by
  have h₁ : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  have h₂ : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  simp_rw [UnitBox_mem, AdmissibleIndex]
  simp_rw [mem_piFinset, Finset.mem_Ico, UnitBoxIndex_apply, sub_nonneg, Int.one_le_ceil_iff,
    mul_pos_iff_of_pos_left h₁, Int.lt_iff_add_one_le, sub_add_cancel, Int.ceil_le,
    ← le_div_iff' h₁, Int.cast_ofNat, div_self h₂]

variable {ι n} in
theorem UnitBoxPart_le_UnitBox {ν : ι → ℤ} :
    UnitBoxPart ι n ν ≤ UnitBox ι ↔ ν ∈ AdmissibleIndex ι n := by
  have h : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  simp_rw [BoxIntegral.Box.le_iff_bounds, UnitBox, UnitBoxPart, AdmissibleIndex, mem_piFinset,
    Finset.mem_Ico, Pi.le_def, ← forall_and, ← add_div, le_div_iff' h, mul_zero,
    Int.cast_nonneg, div_le_iff h, one_mul, ← Int.cast_one (R := ℝ), ← Int.cast_add,
    show ((n:ℕ):ℝ) = (n:ℤ) by rfl, Int.cast_le, ← Int.lt_iff_add_one_le]

variable [DecidableEq (BoxIntegral.Box ι)]

def UnitBoxTaggedPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι) where
  boxes := Finset.image (fun ν ↦ UnitBoxPart ι n ν) (AdmissibleIndex ι n)
  le_of_mem' _ hB := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hB
    exact UnitBoxPart_le_UnitBox.mpr hν
  pairwiseDisjoint := by
    intro _ hB _ hB'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB'
    rw [(UnitBoxPart_injective ι n).ne_iff]
    intro h
    exact (UnitBoxPart_disjoint ι n).mp h
  tag := by
    intro B
    by_cases hB : ∃ ν ∈ AdmissibleIndex ι n, B = UnitBoxPart ι n ν
    · exact UnitBoxTag ι n hB.choose
    · exact 1
  tag_mem_Icc := by
    intro B
    split_ifs with h
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe]
      have t1 := UnitBoxTag_mem_unitBoxPart ι n h.choose
      have t2 := UnitBoxPart_le_UnitBox.mpr h.choose_spec.1
      exact t2 t1
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe, UnitBox_mem]
      intro _
      norm_num

variable {ι n} in
theorem mem_UnitBoxTaggedPrepartition_iff {B : BoxIntegral.Box ι} :
    B ∈ UnitBoxTaggedPrepartition ι n ↔ ∃ ν ∈ AdmissibleIndex ι n, UnitBoxPart ι n ν = B := by
  simp [UnitBoxTaggedPrepartition]

@[simp]
theorem UnitBoxTaggedPrepartition_tag_eq {ν : ι → ℤ} (hν : ν ∈ AdmissibleIndex ι n) :
    (UnitBoxTaggedPrepartition ι n).tag (UnitBoxPart ι n ν) = UnitBoxTag ι n ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have h : ∃ ν' ∈ AdmissibleIndex ι n, UnitBoxPart ι n ν = UnitBoxPart ι n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (UnitBoxTag_injective ι n).eq_iff, ← (UnitBoxPart_injective ι n).eq_iff]
  exact h.choose_spec.2.symm

theorem UnitBoxTaggedPrepartition_isHenstock :
    (UnitBoxTaggedPrepartition ι n).IsHenstock := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  rw [UnitBoxTaggedPrepartition_tag_eq ι n hν]
  exact BoxIntegral.Box.coe_subset_Icc (UnitBoxTag_mem_unitBoxPart ι n ν)

theorem UnitBoxTaggedPrepartition_isPartition :
    (UnitBoxTaggedPrepartition ι n).IsPartition := by
  intro x hx
  use UnitBoxPart ι n (UnitBoxIndex ι n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition_iff]
    exact ⟨UnitBoxIndex ι n x, UnitBox_mem_iff_index.mp hx, rfl⟩
  · exact (UnitBoxPart_mem_iff_index_eq ι n).mpr rfl

theorem UnitBoxTaggedPrepartition_isSubordinate {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition ι n).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  dsimp
  have t1 : Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) ≤ r := by
    refine le_trans (UnitBoxPart_diam ι n ν) ?_
    rw [div_le_iff]
    rwa [div_le_iff hr, mul_comm] at hn
    exact Nat.cast_pos.mpr n.pos
  intro x hx
  rw [Metric.mem_closedBall, UnitBoxTaggedPrepartition_tag_eq ι n hν]
  have t2 : UnitBoxTag ι n ν ∈ (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) := by
    refine BoxIntegral.Box.coe_subset_Icc ?_
    exact UnitBoxTag_mem_unitBoxPart _ _ _
  have t3 := Metric.dist_le_diam_of_mem ?_ hx t2
  exact le_trans t3 t1
  refine IsCompact.isBounded ?_
  exact BoxIntegral.Box.isCompact_Icc (UnitBoxPart ι n ν)

variable (s : Set (ι → ℝ)) (hs₁ : s ≤ UnitBox ι)

abbrev IntegralPoints : Set (ι → ℝ) := ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))

theorem UnitBoxTag_mem_smul_span (ν : ι → ℤ) :
    UnitBoxTag ι n ν ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range]
  refine ⟨?_, ?_⟩
  · exact fun i ↦ ν i + 1
  · refine ⟨?_, ?_⟩
    · intro i
      use ν i + 1
      zify
    · ext i
      rw [Pi.smul_apply, smul_eq_mul, UnitBoxTag]
      ring

theorem UnitBoxTag_eq_of_mem_smul_span {x : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) :
    UnitBoxTag ι n (UnitBoxIndex ι n x) = x := by
  simp_rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set, SetLike.mem_coe,
    Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom,
    Set.mem_range] at hx
  obtain ⟨ν, hν, rfl⟩ := hx
  ext i
  obtain ⟨y, hy⟩ := hν i
  rw [UnitBoxTag, UnitBoxIndex, Pi.smul_apply, ← hy, smul_eq_mul, ← mul_assoc, mul_inv_cancel,
    one_mul, Int.cast_sub, Int.cast_one, sub_add_cancel]
  rw [Int.ceil_intCast]
  ring
  rw [Nat.cast_ne_zero]
  exact PNat.ne_zero n

theorem Index_admissible_of_mem {x : ι → ℝ} (hx : x ∈ IntegralPoints ι n s) :
    UnitBoxIndex ι n x ∈ AdmissibleIndex ι n := by
  rw [← @UnitBox_mem_iff_index]
  refine hs₁ (Set.mem_of_mem_inter_left hx)

def CountingFunction := Nat.card (IntegralPoints ι n s)

theorem CountingFunction_eq :
  CountingFunction ι n s =
    Finset.sum (UnitBoxTaggedPrepartition ι n).toPrepartition.boxes
      fun B ↦ (Set.indicator s (fun x ↦ 1) ((UnitBoxTaggedPrepartition ι n).tag B)) := by
  classical
  rw [Finset.sum_indicator_eq_sum_filter]
  rw [← Finset.card_eq_sum_ones]
  rw [← Nat.card_eq_finsetCard]
  simp_rw [Finset.mem_filter]
  simp_rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
        mem_UnitBoxTaggedPrepartition_iff]
  refine Nat.card_eq_of_bijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨UnitBoxPart ι n (UnitBoxIndex ι n x), ?_, ?_⟩
    · refine ⟨UnitBoxIndex ι n x, ?_, rfl⟩
      rw [← UnitBox_mem_iff_index]
      have := hs₁ (Set.mem_of_mem_inter_left hx)
      exact this
    · rw [UnitBoxTaggedPrepartition_tag_eq]
      · have := Set.mem_of_mem_inter_right hx
        have := UnitBoxTag_eq_of_mem_smul_span ι n this
        rw [← this] at hx
        exact Set.mem_of_mem_inter_left hx
      · rw [← @UnitBox_mem_iff_index]
        exact hs₁ (Set.mem_of_mem_inter_left hx)
  · intro x y h
    simp at h
    rw [(UnitBoxPart_injective _ _).eq_iff] at h
    rw [Subtype.mk.injEq]
    have := UnitBoxTag_eq_of_mem_smul_span ι n (Set.mem_of_mem_inter_right x.mem)
    rw [← this]
    have := UnitBoxTag_eq_of_mem_smul_span ι n (Set.mem_of_mem_inter_right y.mem)
    rw [← this]
    exact congr_arg (UnitBoxTag ι n) h
  · dsimp
    rintro ⟨_, hB, h⟩
    obtain ⟨ν, hν, rfl⟩ := hB
    rw [UnitBoxTaggedPrepartition_tag_eq ι n hν] at h
    dsimp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact UnitBoxTag ι n ν
    · refine Set.mem_inter h ?_
      exact UnitBoxTag_mem_smul_span ι n ν
    · simp only [Subtype.mk.injEq]
      rw [(UnitBoxPart_injective _ _).eq_iff]
      exact UnitBoxIndex_tag ι n ν

theorem UnitBoxTaggedPrepartition_integralSum n :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
       (UnitBoxTaggedPrepartition ι n) = (CountingFunction ι n s : ℝ) / n ^ card ι := by
  classical
  unfold BoxIntegral.integralSum
  rw [CountingFunction_eq, Nat.cast_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hB
  obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hB
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, smul_eq_mul]
  rw [mul_comm, UnitBoxPart_volume]
  congr
  · rw [Set.indicator_apply, Set.indicator_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · norm_num
    rfl
  · exact hs₁

theorem main (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ+ ↦ (CountingFunction ι n s : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  have : ContinuousOn (Set.indicator s (fun _ ↦ (1:ℝ))) (BoxIntegral.Box.Icc (UnitBox ι)) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this
    BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in (UnitBox ι), Set.indicator s (fun x ↦ (1:ℝ)) x = (volume s).toReal := by
    rw [MeasureTheory.integral_indicator_const _ hs₂]
    simp only [smul_eq_mul, mul_one]
    rw [Measure.restrict_eq_self volume hs₁]
  rw [this] at main
  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main (eps / 2) (half_pos h_eps)
  obtain ⟨r, hr₁, hr₂⟩ := main

  specialize hr₁ 0 rfl -- this say that ∀ x, r x = r 0
  --
  specialize hr₂ 0

  let N : ℕ+ := by
    refine ⟨?_, ?_⟩
    exact Nat.ceil (1 / (r 0 0 : ℝ))
    rw [Nat.ceil_pos, one_div, inv_pos]
    exact (r 0 0).mem

  have : ∀ n, N ≤ n →
      BoxIntegral.IntegrationParams.MemBaseSet BoxIntegral.IntegrationParams.Riemann
        (UnitBox ι) 0 (r 0) (UnitBoxTaggedPrepartition ι n) := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 0 = fun _ ↦ r 0 0 := Function.funext_iff.mpr hr₁
      rw [this]
      refine UnitBoxTaggedPrepartition_isSubordinate ι _ _ ?_
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock ι _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h

  use N
  intro n hn

  specialize hr₂ _ (this n hn) (UnitBoxTaggedPrepartition_isPartition ι n)
  rw [UnitBoxTaggedPrepartition_integralSum] at hr₂
  refine lt_of_le_of_lt hr₂ ?_
  exact half_lt_self_iff.mpr h_eps
  exact hs₁
