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
  -- by_cases hx : x ∈ (UnitBox ι).toSet
  -- · intro i
  --   refine ⟨?_, ?_⟩
  --   · exact Nat.ceil ((n * x : ι → ℝ) i) - 1
  --   · rw [Nat.lt_iff_le_pred n.pos, Nat.sub_le_iff_le_add, Nat.sub_add_cancel n.pos, Nat.ceil_le,
  --       Pi.coe_nat, Pi.mul_apply, mul_le_iff_le_one_right]
  --     · exact ((UnitBox_mem ι _).mp hx i).2
  --     · rw [Nat.cast_pos]
  --       exact n.pos
  -- · exact 0

theorem UnitBoxIndex_apply {x : ι → ℝ} (i : ι) :
    UnitBoxIndex ι n x i = Int.ceil (n * (x : ι → ℝ) i) - 1 := rfl
  -- rw [UnitBoxIndex, dif_pos (by exact hx)]
  -- simp

theorem UnitBoxPart_mem_iff_index_eq {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ UnitBoxPart ι n ν ↔ UnitBoxIndex ι n x = ν := by
  rw [UnitBoxPart_mem]
  rw [Function.funext_iff]
  have h_npos : 0 < (n:ℝ) := by
    rw [Nat.cast_pos]
    exact PNat.pos n
  simp_rw [UnitBoxIndex_apply ι n, sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

theorem UnitBox_mem_iff_index {x : ι → ℝ} :
    x ∈ UnitBox ι ↔ ∀ i, 0 ≤ UnitBoxIndex ι n x i ∧ UnitBoxIndex ι n x i < n := sorry

  -- have t1 : ∀ i, 1 ≤ ⌈n * (x : ι → ℝ) i⌉₊ := by
  --   intro i
  --   rw [ Nat.one_le_ceil_iff]
  --   refine mul_pos ?_ ?_
  --   rw [Nat.cast_pos]
  --   exact n.pos
  --   exact ((UnitBox_mem ι _).mp hx i).1
  -- have t2 : ∀ i, (ν i : ℕ) + 1 ≠ 0 := by
  --   intro i
  --   exact Nat.succ_ne_zero _
  -- have t3 : 0 < (n:ℝ) := by
  --   rw [Nat.cast_pos]
  --   exact n.pos
  -- conv_rhs =>
  --   ext i
  --   rw [Nat.sub_eq_iff_eq_add (t1 i), Nat.ceil_eq_iff (t2 i), Nat.add_sub_cancel,
  --     ← _root_.le_div_iff' t3, ← div_lt_iff' t3, Nat.cast_add_one, add_div]

-- Upper right corner
def UnitBoxTag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

theorem UnitBoxTag_mem_unitBoxPart (ν : ι → ℤ) :
    UnitBoxTag ι n ν ∈ UnitBoxPart ι n ν := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxTag, UnitBoxPart, Set.mem_Ioc]
  intro _
  refine ⟨?_, by rw [← add_div]⟩
  rw [div_lt_div_right <| Nat.cast_pos.mpr (PNat.pos n)]
  linarith

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

theorem UnitBoxPart_inj (ν ν' : ι → ℤ) :
    UnitBoxPart ι n ν = UnitBoxPart ι n ν' ↔ ν = ν' := by
  refine ⟨?_, ?_⟩
  · contrapose!
    rw [UnitBoxPart_disjoint]
    exact fun i ↦ BoxIntegral.Box.ne_of_disjoint_coe i
  · intro h
    exact congr_arg (UnitBoxPart ι n ·) h

abbrev UnitBoxPartFin (ν : ι → Fin n) := UnitBoxPart ι n (((↑) : _ → ℤ) ∘ ν)

theorem UnitBoxPart_le_UnitBox (ν : ι → Fin n) :
    UnitBoxPartFin ι n ν ≤ UnitBox ι := by
  simp_rw [BoxIntegral.Box.le_iff_bounds, UnitBox, UnitBoxPartFin, UnitBoxPart]
  simp_rw [Pi.le_def]
  refine ⟨?_, ?_⟩
  · intro _
    simp only [Function.comp_apply, Int.cast_ofNat]
    positivity
  · intro i
    rw [← add_div, div_le_iff, one_mul, Function.comp_apply]
    have := (ν i).prop
    rw [Nat.lt_iff_add_one_le, ← Nat.cast_le (α := ℝ), Nat.cast_add_one] at this
    exact this
    · rw [Nat.cast_pos]
      exact n.pos

variable [Fintype ι]

open scoped Classical in
def UnitBoxTaggedPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι) where
  boxes := Finset.univ.image (fun ν : ι → Fin n ↦ UnitBoxPartFin ι n ν)
  le_of_mem' _ hJ := by
    obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hJ
    exact UnitBoxPart_le_UnitBox ι n ν
  pairwiseDisjoint := by
    intro _ hJ _ hJ'
    obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨ν', _, rfl⟩ := Finset.mem_image.mp hJ'
    rw [ne_eq, UnitBoxPart_inj]
    intro h
    exact (UnitBoxPart_disjoint ι n).mp h
  tag := by
    intro J
    by_cases hJ : ∃ ν : ι → ℤ, J = UnitBoxPart ι n ν
    · exact UnitBoxTag ι n hJ.choose
    · exact 0
  tag_mem_Icc := sorry

theorem mem_UnitBoxTaggedPrepartition (J : BoxIntegral.Box ι) :
    J ∈ UnitBoxTaggedPrepartition ι n ↔ ∃ ν : ι → Fin n, UnitBoxPartFin ι n ν = J := by
  simp [UnitBoxTaggedPrepartition]
  sorry

theorem UnitBoxTaggedPrepartition_isPartition :
    (UnitBoxTaggedPrepartition ι n).IsPartition := by
  intro x hx
  use UnitBoxPart ι n (UnitBoxIndex ι n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition]
    refine ⟨?_, ?_⟩
    let ν := ((↑) : _ → Fin n) ∘ (UnitBoxIndex ι n x)
    use ν
    rw [UnitBoxPart_inj]
    ext i


--    exact ⟨((↑) : _ → Fin n) ∘ (UnitBoxIndex ι n x), rfl⟩
  · exact (UnitBoxPart_mem_iff_index_eq ι n).mpr rfl

#exit


variable {ι} in
theorem UnitBoxPart_mem_icc {ν : ι → Fin n} {x : ι → ℝ} :
    x ∈ BoxIntegral.Box.Icc (UnitBoxPart ι ν) ↔ ∀ i, ν i / n ≤ x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [BoxIntegral.Box.Icc_eq_pi, UnitBoxPart, Set.mem_univ_pi, Set.mem_Icc]





  rw [not_iff_not.symm]
  simp_rw [ne_eq, not_not, Set.not_disjoint_iff, BoxIntegral.Box.mem_coe]
  refine ⟨?_, ?_⟩
  · intro h
    use UnitBoxTag ι ν
    refine ⟨?_, ?_⟩
    · exact UnitBoxTag_mem_unitBoxPart ι ν
    · rw [h]
      exact UnitBoxTag_mem_unitBoxPart ι ν'
  · rintro ⟨x, hx⟩
    simp_rw [UnitBoxPart_mem, ← forall_and] at hx
    ext i
    specialize hx i
    refine le_antisymm ?_ ?_
    · have := lt_of_lt_of_le hx.1.1 hx.2.2
      have := mul_lt_mul_of_pos_right this (?_ : 0 < (n:ℝ))
      rw [add_mul, div_mul_cancel, div_mul_cancel, div_mul_cancel, ← Nat.cast_add_one,
        Nat.cast_lt] at this
      exact Nat.lt_succ.mp this
      any_goals exact NeZero.natCast_ne _ _
      rw [Nat.cast_pos]
      exact PNat.pos n
    · have := lt_of_lt_of_le hx.2.1 hx.1.2
      have := mul_lt_mul_of_pos_right this (?_ : 0 < (n:ℝ))
      rw [add_mul, div_mul_cancel, div_mul_cancel, div_mul_cancel, ← Nat.cast_add_one,
        Nat.cast_lt] at this
      exact Nat.lt_succ.mp this
      any_goals exact NeZero.natCast_ne _ _
      rw [Nat.cast_pos]
      exact PNat.pos n

theorem UnitBoxPart_inj (ν ν' : ι → Fin n) :
    UnitBoxPart ι ν = UnitBoxPart ι ν' ↔ ν = ν' := sorry

theorem UnitBoxPart_upper_sub_lower  (ν : ι → Fin n) (i : ι) :
    (UnitBoxPart ι ν).upper i - (UnitBoxPart ι ν).lower i = 1 / n := by
  simp [UnitBoxPart]





example (ν : ι → Fin n) : Metric.diam (UnitBoxPart ι ν).toSet ≤ 1 / n := by

  suffices EMetric.diam (UnitBoxPart ι ν).toSet ≤ ENNReal.ofReal (1 / n) by
    rw [← ENNReal.toReal_le_toReal] at this
    convert this
    rw [ENNReal.toReal_ofReal]
    positivity
    sorry
    exact ENNReal.ofReal_ne_top
  rw [BoxIntegral.Box.coe_eq_pi]
  refine EMetric.diam_pi_le_of_le ?_
  intro i
  rw [Real.ediam_Ioc, UnitBoxPart]
  rw [add_sub_cancel']



theorem UnitBoxPart_norm_le_of_mem_icc (ν : ι → Fin n) {x : ι → ℝ}
    (hx : x ∈ (BoxIntegral.Box.Icc (UnitBoxPart ι ν))) :
    ‖x - UnitBoxTag ι ν‖ ≤ 1 / n := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Pi.sub_apply]
  rw [Real.norm_eq_abs]
  rw [abs_sub_le_iff, UnitBoxTag]
  rw [UnitBoxPart_mem_icc] at hx
  specialize hx i
  refine ⟨?_, ?_⟩
  · aesop
    sorry
  · aesop
    sorry



theorem UnitBoxTaggedPrepartition_tag_eq (ν : ι → Fin n) :
    (UnitBoxTaggedPrepartition ι n).tag (UnitBoxPart ι ν) = UnitBoxTag ι ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have : ∃ ν' : ι → Fin n, UnitBoxPart ι ν = UnitBoxPart ι ν' := ⟨ν, rfl⟩
  rw [dif_pos this]
  have := this.choose_spec
  rw [UnitBoxPart_inj] at this
  have := congr_arg (UnitBoxTag ι ·) this
  exact this.symm

theorem mem_UnitBoxTaggedPrepartition (J : BoxIntegral.Box ι) :
    J ∈ UnitBoxTaggedPrepartition ι n ↔ ∃ ν : ι → Fin n, UnitBoxPart ι ν = J := by
  simp [UnitBoxTaggedPrepartition]
  sorry

variable (n)

theorem UnitBoxTaggedPrepartition_isHenstock :
    (UnitBoxTaggedPrepartition ι n).IsHenstock := sorry



  sorry

variable {n}

theorem UnitBoxTaggedPrepartition_isSubordinate {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition ι n).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro J hJ
  rw [mem_UnitBoxTaggedPrepartition] at hJ
  obtain ⟨ν, rfl⟩ := hJ
  rw [UnitBoxTaggedPrepartition_tag_eq]
  rw [BoxIntegral.Box.Icc_eq_pi]
  rw [Set.pi_univ_Icc]
  rintro x hx
  rw [Metric.mem_closedBall]
  rw [dist_eq_norm]
  dsimp
  rw [div_le_iff hr, ← div_le_iff'] at hn
  refine le_trans ?_ hn
  exact toto ι ν hx
  rw [Nat.cast_pos]
  exact PNat.pos n

theorem UnitBoxPart_volume (ν : ι → Fin n) :
    (volume (UnitBoxPart ι ν : Set (ι → ℝ))).toReal = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc]
  simp_rw [UnitBoxPart_upper_sub_lower]
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos, ENNReal.toReal_pow, ENNReal.toReal_div,
    div_pow, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, one_pow, Fintype.card]
  any_goals positivity
  refine Nat.cast_pos.mpr n.pos

variable (s : Set (ι → ℝ)) (hs : s ≤ UnitBox ι)

variable {ι} (n)

abbrev IntegralPoints : Set (ι → ℝ) := ↑((n:ℝ) • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)))

variable {s}

theorem IntegralPoints_mem_smul_UnitBox {x : ι → ℝ} (hx : x ∈ IntegralPoints n s) :
    x ∈ (n:ℝ) • (UnitBox ι).toSet :=
  (by aesop : (n:ℝ) • s ≤ (n:ℝ) • (UnitBox ι).toSet) <| Set.mem_of_mem_inter_left hx

theorem IntegralPoints_pos {x : ι → ℝ} (hx : x ∈ IntegralPoints n s) (i : ι) : 0 < x i := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp (IntegralPoints_mem_smul_UnitBox n hs hx)
  rw [BoxIntegral.Box.mem_coe, mem_UnitBox] at hy
  simp only [Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.cast_pos, PNat.pos,
    mul_pos_iff_of_pos_left, hy i]

theorem IntegralPoints_le {x : ι → ℝ} (hx : x ∈ IntegralPoints n s) (i : ι) : x i ≤ n := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp (IntegralPoints_mem_smul_UnitBox n hs hx)
  rw [BoxIntegral.Box.mem_coe, mem_UnitBox] at hy
  simp only [Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.cast_pos, PNat.pos, mul_le_iff_le_one_right,
    ge_iff_le, hy i]

theorem IntegralPoints_integral {x : ι → ℝ} (hx : x ∈ IntegralPoints n s) :
    ∃ v : ι → Fin n, ∀ i, x i = v i + 1 := by
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨Nat.ceil (x i) - 1, ?_⟩
    rw [Nat.lt_iff_le_pred, Nat.sub_le_iff_le_add, Nat.sub_add_cancel, Nat.ceil_le]
    exact IntegralPoints_le n hs hx i
    rw [Nat.succ_le]
    all_goals exact PNat.pos n
  · intro i
    have h_pos := IntegralPoints_pos n hs hx i
    dsimp only
    simp_rw [Set.mem_inter_iff, SetLike.mem_coe, Basis.mem_span_iff_repr_mem, Pi.basisFun_repr,
      algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range] at hx
    obtain ⟨y, hy⟩ := hx.2 i
    rw [Nat.cast_sub, Nat.cast_one, sub_add_cancel, ← hy, Nat.ceil_intCast]
    rw [show (Int.toNat y : ℝ) = (Int.toNat y : ℤ) by rfl]
    rw [Int.toNat_of_nonneg]
    rw [← Int.cast_nonneg (α := ℝ), hy]
    refine le_of_lt h_pos
    rw [Nat.one_le_ceil_iff]
    exact h_pos

theorem IntegralPoints_mem_iff (x : ι → ℝ) :
    x ∈ IntegralPoints n s ↔ (x ∈ (n:ℝ) • s ∧ ∃ y : ι → Fin n, ∀ i, x i = y i + 1) := by
  refine ⟨?_, ?_⟩
  · intro hx
    obtain ⟨ν, hν⟩ := IntegralPoints_integral n hs hx
    refine ⟨?_, ⟨ν, hν⟩⟩
    exact Set.mem_of_mem_inter_left hx
  · intro hx
    rw [Set.mem_inter_iff]
    refine ⟨hx.1, ?_⟩
    simp_rw [SetLike.mem_coe, Basis.mem_span_iff_repr_mem, Pi.basisFun_repr,
      algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range]
    intro i
    obtain ⟨y, hy⟩ := hx.2
    use y i + 1
    rw [hy i]
    simp only [Int.cast_add, Int.cast_ofNat, Int.cast_one]

variable (s) in
def CountingFunction := Nat.card (IntegralPoints n s)

def UnitBoxPart_index (x : IntegralPoints n s) : ι → Fin n :=
    (IntegralPoints_integral n hs x.mem).choose

theorem UnitBoxPart_index_inj {x : IntegralPoints n s} {y : IntegralPoints n s} :
    UnitBoxPart_index n hs x = UnitBoxPart_index n hs y ↔ x = y := by
  have t1 := (IntegralPoints_integral n hs x.mem).choose_spec
  have t2 := (IntegralPoints_integral n hs y.mem).choose_spec
  rw [UnitBoxPart_index, UnitBoxPart_index]
  rw [Subtype.ext_iff]
  simp_rw [Function.funext_iff, t1, t2, add_left_inj, Nat.cast_inj, Fin.ext_iff]

theorem UnitBoxTag_index_eq (x : IntegralPoints n s) :
    UnitBoxTag ι (UnitBoxPart_index n hs x) = (1 / (n : ℝ)) • x := by
  sorry
  -- ext i
  -- dsimp only [UnitBoxTag, UnitBoxPart_index]
  -- have h_posx : 0 < x i := IntegralPoints_pos n s hx i
  -- simp_rw [Set.mem_inter_iff, SetLike.mem_coe, Basis.mem_span_iff_repr_mem, Pi.basisFun_repr,
  --   algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range] at hx
  -- rw [Pi.smul_apply, smul_eq_mul]
  -- obtain ⟨y, hy⟩ := hx.2 i
  -- have h_posy : 0 < y := by
  --   rw [← Int.cast_pos (α := ℝ), hy]
  --   exact h_posx
  -- obtain ⟨z, rfl⟩ : ∃ z : ℕ+, y = z := by
  --   refine ⟨⟨Int.natAbs y, ?_⟩, ?_⟩
  --   · rw [Int.natAbs_pos]
  --     exact ne_of_gt h_posy
  --   · rw [PNat.mk_coe, Int.coe_natAbs, abs_eq_self.mpr (le_of_lt h_posy)]
  -- rw [← hy, Int.cast_ofNat, Nat.ceil_natCast]
  -- rw [Nat.cast_sub, Nat.cast_one]
  -- rw [sub_add_cancel]
  -- field_simp
  -- exact z.prop

theorem UnitBoxTag_index_mem (x : IntegralPoints n s) :
    UnitBoxTag ι (UnitBoxPart_index n hs x) ∈ s := by
  rw [UnitBoxTag_index_eq]
  obtain ⟨y, hy, h_eq⟩ := x.mem.1
  simp [← h_eq, hy]

theorem UnitBoxTag_index_tag {ν : ι → Fin n} (hν : (n:ℝ) • UnitBoxTag ι ν ∈ IntegralPoints n s) :
    UnitBoxPart_index n hs ⟨_, hν⟩  = ν := by
  sorry
  -- ext i
  -- dsimp only [UnitBoxPart_index]
  -- rw [Pi.smul_apply, smul_eq_mul, UnitBoxTag]
  -- rw [mul_div_cancel']
  -- rw [← Nat.cast_add_one]
  -- rw [Nat.ceil_natCast]
  -- rw [Nat.add_sub_cancel]
  -- rw [ne_eq, Nat.cast_eq_zero]
  -- exact PNat.ne_zero n

def IntegralPoints_map (x : IntegralPoints n s) : BoxIntegral.Box ι :=
  UnitBoxPart ι (UnitBoxPart_index n hs x)

theorem IntegralPoints_map_tag (x : IntegralPoints n s) :
    (UnitBoxTaggedPrepartition ι n).tag (IntegralPoints_map n hs x) =
      UnitBoxTag ι (UnitBoxPart_index n hs x) := by
  rw [IntegralPoints_map, UnitBoxTaggedPrepartition_tag_eq]

theorem IntegralPoints_map_injective :
    Function.Injective (IntegralPoints_map n hs) := by
  intro _ _ h
  rwa [IntegralPoints_map, IntegralPoints_map, UnitBoxPart_inj, UnitBoxPart_index_inj] at h

theorem UnixBoxTag_mem_of_mem (ν : ι → Fin n)
    (h : (UnitBoxTaggedPrepartition ι n).tag (UnitBoxPart ι ν) ∈ s) :
    (n:ℝ) • UnitBoxTag ι ν ∈ IntegralPoints n s := sorry

theorem CountingFunction_eq :
  CountingFunction n s =
    Finset.sum (UnitBoxTaggedPrepartition ι n).toPrepartition.boxes
      fun J ↦ (Set.indicator s (fun x ↦ 1) ((UnitBoxTaggedPrepartition ι n).tag J)) := by
  rw [Finset.sum_indicator_eq_sum_filter]
  rw [← Finset.card_eq_sum_ones]
  rw [← Nat.card_eq_finsetCard]
  simp_rw [Finset.mem_filter]
  refine Nat.card_eq_of_bijective (fun x ↦ ⟨IntegralPoints_map n hs x, ?_⟩) ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
        mem_UnitBoxTaggedPrepartition]
      use UnitBoxPart_index n hs x
      rfl
    · rw [IntegralPoints_map_tag]
      exact UnitBoxTag_index_mem _ _ _
  · intro a b h
    rw [Subtype.ext_iff] at h
    exact IntegralPoints_map_injective n hs h
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
      mem_UnitBoxTaggedPrepartition] at hJ
    obtain ⟨ν, rfl⟩ := hJ
    refine ⟨⟨(n:ℝ) • UnitBoxTag ι ν, ?_⟩, ?_⟩
    · exact UnixBoxTag_mem_of_mem _ _ hJ'
    · rw [Subtype.mk_eq_mk, IntegralPoints_map, UnitBoxPart_inj]
      exact UnitBoxTag_index_tag n hs _

variable (ι) in
theorem UnitBoxTaggedPrepartition_integralSum n :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
       (UnitBoxTaggedPrepartition ι n) = (CountingFunction n s : ℝ) / n ^ card ι := by
  unfold BoxIntegral.integralSum
  rw [CountingFunction_eq _ hs, Nat.cast_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hJ
  obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hJ
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, smul_eq_mul]
  rw [mul_comm, UnitBoxPart_volume]
  congr
  · rw [Set.indicator_apply, Set.indicator_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · norm_num
    rfl

example :
    Tendsto (fun n : ℕ+ ↦ (CountingFunction n s : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  have : ContinuousOn (Set.indicator s (fun _ ↦ (1:ℝ))) (BoxIntegral.Box.Icc (UnitBox ι)) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in (UnitBox ι), Set.indicator s (fun x ↦ (1:ℝ)) x = (volume s).toReal := by sorry
  rw [this] at main
  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main (eps / 2) sorry -- h_eps
  obtain ⟨r, hr₁, hr₂⟩ := main
  specialize hr₁ 1 rfl -- this say that ∀ x, r x = r 0
  --
  specialize hr₂ 1
  let π := UnitBoxTaggedPrepartition ι 1
  specialize hr₂ π
  have :
      BoxIntegral.IntegrationParams.MemBaseSet BoxIntegral.IntegrationParams.Riemann
        (UnitBox ι) 1 (r 1) π := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 1 = fun _ ↦ ⟨r 1 0, sorry⟩ := sorry
      rw [this]
      exact UnitBoxTaggedPrepartition_isSubordinate ι _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock ι 1
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
  specialize hr₂ this (UnitBoxTaggedPrepartition_isPartition ι _)
  dsimp at hr₂
  rw [UnitBoxTaggedPrepartition_integralSum] at hr₂
  use n
  intro n hn
  -- refine lt_of_le_of_lt hr₂ ?_


  sorry

#exit

example : Tendsto (fun r : ℕ ↦ (CountingFunction s r : ℝ≥0) / r ^ card ι) atTop
  (nhds (volume s)) := by


#exit

  le_of_mem' := by
    rintro _ hJ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    exact UnitBoxPart_le_UnitBox ι hn k
  pairwiseDisjoint := by
    intro _ hJ _ hK h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hK
    have : k ≠ l := by
      rwa [ne_eq, UnitBoxPart_eq_iff] at h
    exact UnitBoxPart_disjoint ι hn this
  tag := by
    intro J
    exact if J ≤ UnitBox ι then J.lower else fun _ ↦ 0
  tag_mem_Icc := by -- this can probably be simplified
    intro J
    split_ifs with h
    · dsimp
      rw [BoxIntegral.Box.le_iff_bounds] at h
      rw [BoxIntegral.Box.Icc_def, Set.mem_Icc]
      refine ⟨h.1, ?_⟩
      simp_rw [Pi.le_def] at h ⊢
      intro i
      have := J.lower_lt_upper i
      refine le_trans (le_of_lt this) (h.2 i)
    · simp [UnitBox, BoxIntegral.Box.Icc_def, Pi.le_def]

#exit

def UnitBoxPart (k :ℕ) : BoxIntegral.Box ι where
  lower := fun _ ↦ k / n
  upper :=  fun _ ↦ (k + 1) /n
  lower_lt_upper := fun _ ↦ (div_lt_div_right (Nat.cast_pos.mpr hn)).mpr (by linarith)

theorem mem_UnitBoxPart {k : Fin n} {x : ι → ℝ} :
    x ∈ UnitBoxPart ι hn k ↔ ∀ i, k / n < x i ∧ x i ≤ (k + 1) / n := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxPart, Set.mem_Ioc]

theorem UnitBoxPart_lower_lt_upper_iff {k l : Fin n} {i : ι} :
    (UnitBoxPart ι hn k).lower i < (UnitBoxPart ι hn l).upper i ↔ k ≤ l := by
  rw [UnitBoxPart, UnitBoxPart, div_lt_div_right (Nat.cast_pos.mpr hn), ← Nat.cast_one,
    ← Nat.cast_add, Nat.cast_lt, Fin.le_def, Nat.lt_succ]

theorem UnitBoxPart_le_UnitBox (k : Fin n) :
    UnitBoxPart ι hn k ≤ UnitBox ι := by
  rw [BoxIntegral.Box.le_iff_bounds]
  refine ⟨?_, ?_⟩
  · intro _
    dsimp only [UnitBox, UnitBoxPart]
    positivity
  · intro _
    dsimp only [UnitBox, UnitBoxPart]
    rw [div_le_iff (Nat.cast_pos.mpr hn), one_mul, ← Nat.cast_one, ← Nat.cast_add,
      Nat.cast_le]
    exact k.prop

theorem UnitBoxPart_disjoint [hι : Nonempty ι] {k l : Fin n} (h : k ≠ l) :
    Disjoint (UnitBoxPart ι hn k).toSet (UnitBoxPart ι hn l).toSet := by
  rw [Set.disjoint_right]
  intro a ha
  simp_rw [BoxIntegral.Box.mem_coe, BoxIntegral.Box.mem_def, Set.mem_Ioc] at ha ⊢
  push_neg
  obtain ⟨i⟩ := hι
  refine ⟨i, ?_⟩
  specialize ha i
  intro h₁
  have t1 := lt_of_lt_of_le h₁ ha.2
  by_contra! h₂
  have t2 := lt_of_lt_of_le ha.1 h₂
  rw [UnitBoxPart_lower_lt_upper_iff] at t1 t2
  exact h (le_antisymm t1 t2)

variable {ι} {hn} in
theorem UnitBoxPart_eq_iff {k l : Fin n} :
  UnitBoxPart ι hn k = UnitBoxPart ι hn l ↔ k = l := sorry

variable [Nonempty ι]

def UnitBoxPrepartition : BoxIntegral.Prepartition (UnitBox ι) where
  boxes := Finset.univ.image (fun k : Fin n ↦ UnitBoxPart ι hn k)
  le_of_mem' := by
    rintro _ hJ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    exact UnitBoxPart_le_UnitBox ι hn k
  pairwiseDisjoint := by
    intro _ hJ _ hK h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hK
    have : k ≠ l := by
      rwa [ne_eq, UnitBoxPart_eq_iff] at h
    exact UnitBoxPart_disjoint ι hn this

def UnitBoxTaggedPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι) where
  boxes := Finset.univ.image (fun k : Fin n ↦ UnitBoxPart ι hn k)
  le_of_mem' := by
    rintro _ hJ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    exact UnitBoxPart_le_UnitBox ι hn k
  pairwiseDisjoint := by
    intro _ hJ _ hK h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hK
    have : k ≠ l := by
      rwa [ne_eq, UnitBoxPart_eq_iff] at h
    exact UnitBoxPart_disjoint ι hn this
  tag := by
    intro J
    exact if J ≤ UnitBox ι then J.lower else fun _ ↦ 0
  tag_mem_Icc := by -- this can probably be simplified
    intro J
    split_ifs with h
    · dsimp
      rw [BoxIntegral.Box.le_iff_bounds] at h
      rw [BoxIntegral.Box.Icc_def, Set.mem_Icc]
      refine ⟨h.1, ?_⟩
      simp_rw [Pi.le_def] at h ⊢
      intro i
      have := J.lower_lt_upper i
      refine le_trans (le_of_lt this) (h.2 i)
    · simp [UnitBox, BoxIntegral.Box.Icc_def, Pi.le_def]

theorem toto {x : ι → ℝ} (hx : x ∈ UnitBox ι) :
  ∃ J ∈ UnitBoxTaggedPrepartition ι hn, x ∈ J := sorry

theorem UnitBoxTaggedPrepartition_isPartition : (UnitBoxTaggedPrepartition ι hn).IsPartition := by
  rw [BoxIntegral.TaggedPrepartition.isPartition_iff_iUnion_eq]
  ext
  simp
  sorry

variable [Fintype ι]

def μ := MeasureTheory.Measure.toBoxAdditive (volume : Measure (ι → ℝ))

variable (f : (ι → ℝ) → ℝ) (hf : IntegrableOn f (UnitBox ι))



example : 1 = 0 := by
  let l := BoxIntegral.IntegrationParams.McShane
  let F := l.toFilteriUnion (UnitBox ι) (UnitBoxPrepartition ι hn)
  have := hf.hasBoxIntegral l rfl











end

#exit

noncomputable section

open Submodule Filter Bornology MeasureTheory Zspan Fintype ENNReal

open scoped Pointwise NNReal Classical

variable {ι : Type*} [Fintype ι]

variable (b : Basis ι ℝ (ι → ℝ))

variable (s : Set (ι → ℝ)) (hs : MeasurableSet s) (hb : IsBounded s)

theorem finite (c : ℝ) : Set.Finite (c • s ∩ span ℤ (Set.range b) : Set (ι → ℝ)) := by
  change  Set.Finite (c • s ∩ (span ℤ (Set.range b)).toAddSubgroup)
  exact Metric.finite_isBounded_inter_isClosed (IsBounded.smul₀ hb c) inferInstance

-- instance (c : ℝ) : Fintype  (c • s ∩ span ℤ (Set.range b) : Set (ι → ℝ)) := sorry

def Nr : ℝ → ℕ := fun c ↦ Nat.card (c • s ∩ span ℤ (Set.range b) : Set (ι → ℝ))

def P (s : Set (ι → ℝ)) : Prop :=
  Tendsto (fun c : ℝ≥0 ↦ (volume (fundamentalDomain b)) * (Nr b s c : ℝ≥0∞) / c ^ card ι) atTop
    (nhds (volume s))

set_option maxHeartbeats 500000 in
example : P (Pi.basisFun ℝ ι) ((Pi.basisFun ℝ ι).parallelepiped) := by
  dsimp only [P]
  have h_vol : volume ((Pi.basisFun ℝ ι).parallelepiped : Set (ι → ℝ)) = 1 := by
    rw [← addHaarMeasure_eq_volume_pi]
    rw [Basis.parallelepiped_basisFun]
    exact Measure.addHaarMeasure_self
  simp_rw [h_vol]
  have t0 : Tendsto (fun _ : ℝ≥0 ↦ (1:ℝ≥0∞)) atTop (nhds 1) := by
    exact tendsto_const_nhds
  have t1 : Tendsto (fun c : ℝ≥0 ↦ (c + 1 : ℝ≥0∞) ^ card ι / c ^ card ι) atTop (nhds 1) := by
    sorry
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le t0 t1 ?_ ?_
  have main :
      ∀ c, 0 < c → Nr (Pi.basisFun ℝ ι) ((Pi.basisFun ℝ ι).parallelepiped) c
        = (Nat.floor c + 1) ^ card ι := by
    intro c hc
    dsimp only [Nr]
    rw [Basis.parallelepiped_basisFun]
    have : (TopologicalSpace.PositiveCompacts.piIcc01 ι : Set (ι → ℝ)) =
      Set.pi Set.univ fun _ ↦  Set.Icc 0 1 := rfl
    rw [this]
    rw [smul_pi₀]
    simp_rw [Pi.smul_def]
    have : c • Set.Icc 0 1 = Set.Icc 0 c := by sorry
    simp_rw [this]
    have : (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ ↦ Set.range Int.cast := by
      ext; simp [Basis.mem_span_iff_repr_mem]
    rw [this]
    rw [← Set.pi_inter_distrib]
    have : Set.Icc 0 c ∩ Set.range Int.cast =
      ((Nat.cast '' (Set.Icc 0 (Nat.floor c))).toFinset : Finset ℝ) := sorry -- Set.toFinset_Icc
    simp_rw [this]
    rw [← Fintype.coe_piFinset]
    rw [Nat.card_eq_card_toFinset]
    rw [Finset.toFinset_coe]
    rw [card_piFinset]
    rw [Finset.prod_const]
    rw [Set.toFinset_image]
    rw [Set.toFinset_Icc]
    rw [Finset.card_univ]
    rw [Finset.card_image_of_injective]
    rw [Nat.card_Icc]
    rw [tsub_zero]
    exact Nat.cast_injective
    positivity

#exit
    dsimp only [Basis.coe_parallelepiped, Nr]
    have := finite (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι).parallelepiped sorry c
    let S := (c • parallelepiped (Pi.basisFun ℝ ι)) ∩ (span ℤ (Set.range (Pi.basisFun ℝ ι)))
    have : Fintype S := sorry
    rw [Nat.card_eq_fintype_card, parallelepiped]

    sorry
  · intro c
    dsimp only
    rw [volume_fundamentalDomain_pi_basisFun, one_mul, main _ (NNReal.coe_nonneg c)]
    rw [← coe_nat, ← coe_pow, ← coe_div, ← coe_one, coe_le_coe, Nat.cast_pow, ← div_pow]

    have := Nat.le_ceil c
    norm_num [this]




    norm_num [this]
    sorry

  ·
    sorry
