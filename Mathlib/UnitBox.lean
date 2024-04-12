import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Topology.Algebra.Order.Floor

section SpecificLimits

open Filter Topology

theorem tendsto_nat_ceil_div_floor_atTop {R : Type*} [TopologicalSpace R] [LinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    Filter.Tendsto (fun (x : R) => (Nat.ceil x : R) / (Nat.floor x)) Filter.atTop (𝓝 1) := by
  rw [show (1 : R) = 1 * 1⁻¹ by ring]
  refine Tendsto.congr' ?_
      <| tendsto_nat_ceil_div_atTop.mul (tendsto_nat_floor_div_atTop.inv₀ (one_ne_zero))
  filter_upwards [eventually_ne_atTop 0] with _ h
  rw [mul_comm_div, inv_div, div_div, div_mul_cancel_right₀ h, div_eq_mul_inv]

end SpecificLimits

section Order

open Filter Nat

variable {α : Type*} [LinearOrderedSemiring α] [FloorSemiring α]
theorem tendsto_natCeil_atTop : Tendsto (ceil : α → ℕ) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b ↦ ⟨b, (ceil_natCast _).ge⟩

theorem tendsto_natFloor_atTop : Tendsto (floor : α → ℕ) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b ↦
    ⟨(b + 1 : ℕ), by rw [floor_coe]; exact Nat.le_add_right b 1⟩

end Order

section Zspan

open Submodule

open scoped Pointwise

-- Generalize more (IsScalarTower?) and move to other namespace

variable {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (b : Basis ι R M)

theorem Zspan.smul {c : R} (h : IsUnit c) :
    c • span ℤ (Set.range b) = span ℤ (Set.range (b.isUnitSMul (fun _ ↦ h))) := by
  rw [smul_span, Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

end Zspan

section Box

theorem BoxIntegral.Box.IsBounded_Icc {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded (BoxIntegral.Box.Icc B) := B.isCompact_Icc.isBounded

theorem BoxIntegral.Box.IsBounded {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded B.toSet :=
  Bornology.IsBounded.subset (BoxIntegral.Box.IsBounded_Icc B) coe_subset_Icc

end Box

noncomputable section

namespace BoxIntegral

open Bornology MeasureTheory Fintype Submodule

variable {ι : Type*} (n : ℕ+)

def UnitBoxPart (ν : ι → ℤ) : BoxIntegral.Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ ν i / n + 1 / n
  lower_lt_upper := fun _ ↦ by norm_num

@[simp]
theorem UnitBoxPart_mem {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ UnitBoxPart n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBoxPart, Set.mem_Ioc]

def UnitBoxIndex (x : ι → ℝ) : ι → ℤ := fun i ↦ Int.ceil (n * x i) - 1

@[simp]
theorem UnitBoxIndex_apply {x : ι → ℝ} (i : ι) :
    UnitBoxIndex n x i = Int.ceil (n * (x : ι → ℝ) i) - 1 := rfl

variable {n} in
theorem UnitBoxPart_mem_iff_index_eq {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ UnitBoxPart n ν ↔ UnitBoxIndex n x = ν := by
  rw [UnitBoxPart_mem, Function.funext_iff]
  have h_npos : 0 < (n:ℝ) := Nat.cast_pos.mpr <| PNat.pos n
  simp_rw [UnitBoxIndex_apply n, sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel_right, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

-- Upper right corner
def UnitBoxTag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

theorem UnitBoxTag_injective : Function.Injective (fun ν : ι → ℤ ↦ UnitBoxTag n ν) := by
  intro _ _ h
  ext i
  have := congr_arg (fun x ↦ x i) h
  dsimp [UnitBoxTag] at this
  field_simp at this
  exact this

theorem UnitBoxTag_mem_unitBoxPart (ν : ι → ℤ) :
    UnitBoxTag n ν ∈ UnitBoxPart n ν := by
  simp_rw [Box.mem_def, UnitBoxTag, UnitBoxPart, Set.mem_Ioc]
  refine fun _ ↦ ⟨?_, by rw [← add_div]⟩
  rw [div_lt_div_right <| Nat.cast_pos.mpr (PNat.pos n)]
  linarith

@[simp]
theorem UnitBoxIndex_tag (ν : ι → ℤ) :
    UnitBoxIndex n (UnitBoxTag n ν) = ν := by
  rw [← UnitBoxPart_mem_iff_index_eq]
  exact UnitBoxTag_mem_unitBoxPart n ν

theorem UnitBoxPart_disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (UnitBoxPart n ν).toSet (UnitBoxPart n ν').toSet := by
  rw [not_iff_not.symm, ne_eq, not_not, Set.not_disjoint_iff]
  simp_rw [Box.mem_coe]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ?_⟩
  · exact ⟨UnitBoxTag n ν, UnitBoxTag_mem_unitBoxPart n ν, h ▸ UnitBoxTag_mem_unitBoxPart n ν⟩
  · rw [← UnitBoxPart_mem_iff_index_eq.mp hx, ← UnitBoxPart_mem_iff_index_eq.mp hx']

theorem UnitBoxPart_injective : Function.Injective (fun ν : ι → ℤ ↦ UnitBoxPart n ν) := by
  intro _ _ h
  contrapose! h
  rw [UnitBoxPart_disjoint] at h
  exact Box.ne_of_disjoint_coe h

variable [Fintype ι]

theorem UnitBoxPart_diam (ν : ι → ℤ) :
    Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart n ν)) ≤ 1 / n := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine EMetric.diam_pi_le_of_le (fun i ↦ ?_)
  rw [Real.ediam_Icc, UnitBoxPart, add_sub_cancel_left, ENNReal.ofReal_div_of_pos,
    ENNReal.ofReal_one]
  exact Nat.cast_pos.mpr n.pos

@[simp]
theorem UnitBoxPart_volume (ν : ι → ℤ) :
    volume (UnitBoxPart n ν : Set (ι → ℝ)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc, UnitBoxPart,
    add_sub_cancel_left]
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.pos), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast, Finset.card_univ, one_div, one_div, ENNReal.inv_pow]

theorem UnitBoxIndex_setFinite_of_finite_measure {s : Set (ι → ℝ)} (hm : NullMeasurableSet s)
    (hs : volume s ≠ ⊤) :
    Set.Finite {ν : ι → ℤ | ↑(UnitBoxPart n ν) ⊆ s} := by
  have := Measure.finite_const_le_meas_of_disjoint_iUnion₀
    (volume : Measure (ι → ℝ)) (ε := 1 / n ^ card ι) (by norm_num)
    (As := fun ν : ι → ℤ ↦ (UnitBoxPart n ν) ∩ s) ?_ ?_ ?_
  · refine this.subset ?_
    intro ν hν
    rw [Set.mem_setOf, Set.inter_eq_self_of_subset_left hν, UnitBoxPart_volume]
  · intro ν
    refine NullMeasurableSet.inter ?_ hm
    exact (UnitBoxPart n ν).measurableSet_coe.nullMeasurableSet
  · intro ν ν' h
    have := (UnitBoxPart_disjoint n).mp h
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_iff_inter_eq_empty]
    dsimp only
    rw [Set.inter_inter_inter_comm]
    rw [Set.disjoint_iff_inter_eq_empty] at this
    rw [this]
    rw [Set.empty_inter]
  · rw [← lt_top_iff_ne_top]
    refine measure_lt_top_of_subset ?_ hs
    aesop

def UnitBoxIndexAdmissible (B : Box ι) : Finset (ι → ℤ) := by
  let A := {ν : ι → ℤ | UnitBoxPart n ν ≤ B}
  refine Set.Finite.toFinset (s := A) ?_
  refine UnitBoxIndex_setFinite_of_finite_measure n ?_ ?_
  · exact B.measurableSet_coe.nullMeasurableSet
  · rw [← lt_top_iff_ne_top]
    refine IsBounded.measure_lt_top ?_
    exact Box.IsBounded B

variable {n} in
theorem UnitBoxIndexAdmissible_iff {B : Box ι} {ν : ι → ℤ} :
    ν ∈ UnitBoxIndexAdmissible n B ↔ UnitBoxPart n ν ≤ B := by
  rw [UnitBoxIndexAdmissible, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

open Classical in
def UnitBoxTaggedPrepartition (B : Box ι) : BoxIntegral.TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ UnitBoxPart n ν) (UnitBoxIndexAdmissible n B)
  le_of_mem' _ hB := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hB
    exact UnitBoxIndexAdmissible_iff.mp hν
  pairwiseDisjoint := by
    intro _ hB _ hB' h
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hB'
    exact (UnitBoxPart_disjoint n).mp fun h' ↦ h (congrArg (UnitBoxPart n) h')
  tag := by
    intro B'
    by_cases hB' : ∃ ν ∈ UnitBoxIndexAdmissible n B, B' = UnitBoxPart n ν
    · exact UnitBoxTag n hB'.choose
    · exact B.exists_mem.choose
  tag_mem_Icc := by
    intro B'
    split_ifs with hB'
    · have := hB'.choose_spec.1
      rw [UnitBoxIndexAdmissible_iff] at this
      refine Box.coe_subset_Icc ?_
      refine this ?_
      exact UnitBoxTag_mem_unitBoxPart n (Exists.choose hB')
    · exact Box.coe_subset_Icc (B.exists_mem.choose_spec)

variable {n} in
@[simp]
theorem UnitBoxTaggedPrepartition_mem_iff {B B' : Box ι} :
    B' ∈ UnitBoxTaggedPrepartition n B ↔
      ∃ ν ∈ UnitBoxIndexAdmissible n B, UnitBoxPart n ν = B' := by
  classical
  rw [UnitBoxTaggedPrepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk, Finset.mem_image]

theorem UnitBoxTaggedPrepartition_tag_eq {ν : ι → ℤ} (B : Box ι)
    (hν : ν ∈ UnitBoxIndexAdmissible n B) :
    (UnitBoxTaggedPrepartition n B).tag (UnitBoxPart n ν) = UnitBoxTag n ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have h : ∃ ν' ∈ UnitBoxIndexAdmissible n B, UnitBoxPart n ν = UnitBoxPart n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (UnitBoxTag_injective n).eq_iff, ← (UnitBoxPart_injective n).eq_iff]
  exact h.choose_spec.2.symm

theorem UnitBoxTaggedPrepartition_isHenstock (B : Box ι) :
    (UnitBoxTaggedPrepartition n B).IsHenstock := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := UnitBoxTaggedPrepartition_mem_iff.mp hB
  rw [UnitBoxTaggedPrepartition_tag_eq n B hν]
  exact BoxIntegral.Box.coe_subset_Icc (UnitBoxTag_mem_unitBoxPart n ν)

def HasIntegralVertices (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

variable {n} in
theorem UnitBoxIndex_memAdmissible_iff' {x : ι → ℝ} {B : Box ι} :
  UnitBoxIndex n x ∈ UnitBoxIndexAdmissible n B ↔
    ∀ i, n * B.lower i + 1 ≤ Int.ceil (n * x i) ∧ Int.ceil (n * x i) ≤ n * B.upper i  := by
  simp_rw [UnitBoxIndexAdmissible_iff, Box.le_iff_bounds, UnitBoxPart, UnitBoxIndex, Pi.le_def,
    ← forall_and]
  have : (0:ℝ) < n := Nat.cast_pos.mpr n.pos
  simp_rw [Int.cast_sub, Int.cast_one, ← add_div, le_div_iff' this, div_le_iff' this,
    sub_add_cancel, le_sub_iff_add_le]

theorem UnixBoxIndexAdmissible_of_mem_box {B : Box ι} (hB : HasIntegralVertices B)
    {x : ι → ℝ} (hx : x ∈ B) :
    UnitBoxIndex n x ∈ UnitBoxIndexAdmissible n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  rw [UnitBoxIndex_memAdmissible_iff']
  intro i
  rw [hl i, hu i, show ((n : ℕ) : ℝ) = (n : ℤ) by rfl, ← Int.cast_mul, ← Int.cast_mul,
    ← Int.cast_one, ← Int.cast_add, Int.cast_le, Int.cast_le, Int.ceil_le]
  rw [Int.add_one_le_ceil_iff, Int.cast_mul, Int.cast_mul, mul_lt_mul_left, _root_.mul_le_mul_left]
  simp_rw [Box.mem_def, Set.mem_Ioc, hl, hu] at hx
  exact hx i
  exact Nat.cast_pos.mpr n.pos
  exact Nat.cast_pos.mpr n.pos

theorem UnitBoxPart_index_mem {B : Box ι} (hB : HasIntegralVertices B) {x : ι → ℝ} (hx : x ∈ B) :
    UnitBoxPart n (UnitBoxIndex n x) ∈ UnitBoxTaggedPrepartition n B := by
  rw [UnitBoxTaggedPrepartition_mem_iff]
  refine ⟨UnitBoxIndex n x, ?_, rfl⟩
  exact UnixBoxIndexAdmissible_of_mem_box n hB hx

theorem UnitBoxTaggedPrepartition_isPartition {B : Box ι} (hB : HasIntegralVertices B) :
    (UnitBoxTaggedPrepartition n B).IsPartition := by
  intro x hx
  use UnitBoxPart n (UnitBoxIndex n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, UnitBoxTaggedPrepartition_mem_iff]
    refine ⟨UnitBoxIndex n x, ?_, rfl⟩
    exact UnixBoxIndexAdmissible_of_mem_box n hB hx
  · exact UnitBoxPart_mem_iff_index_eq.mpr rfl

theorem UnitBoxTaggedPrepartition_isSubordinate (B : Box ι) {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition n B).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := UnitBoxTaggedPrepartition_mem_iff.mp hB
  dsimp
  have t1 : Metric.diam (Box.Icc (UnitBoxPart n ν)) ≤ r := by
    refine le_trans (UnitBoxPart_diam n ν) ?_
    rw [div_le_iff]
    rwa [div_le_iff hr, mul_comm] at hn
    exact Nat.cast_pos.mpr n.pos
  intro x hx
  rw [Metric.mem_closedBall, UnitBoxTaggedPrepartition_tag_eq n B hν]
  have t2 : UnitBoxTag n ν ∈ (BoxIntegral.Box.Icc (UnitBoxPart n ν)) := by
    refine Box.coe_subset_Icc ?_
    exact UnitBoxTag_mem_unitBoxPart _ _
  have t3 := Metric.dist_le_diam_of_mem ?_ hx t2
  exact le_trans t3 t1
  refine IsCompact.isBounded ?_
  exact BoxIntegral.Box.isCompact_Icc (UnitBoxPart n ν)

theorem le_hasIntegralVertices_of_isBounded {ι : Type*} [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, HasIntegralVertices B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt h 0 0
  let C : ℕ+ := ⟨Nat.ceil R, Nat.ceil_pos.mpr hR₁⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine BoxIntegral.Box.mk (fun _ ↦ - C) (fun _ ↦ C ) ?_
    intro _
    norm_num [hR₁]
  · exact fun _ ↦ - C
  · exact fun _ ↦ C
  · simp
  · intro x hx
    have t1 : Metric.ball (0 : ι → ℝ) R ⊆ Metric.ball 0 C := by
      refine Metric.ball_subset_ball ?h
      exact Nat.le_ceil R
    have := hR₂ hx
    have := t1 this
    rw [mem_ball_zero_iff] at this
    rw [pi_norm_lt_iff] at this
    · simp_rw [Real.norm_eq_abs, abs_lt] at this
      simp only [Box.mem_coe, Box.mem_mk, Set.mem_Ioc]
      refine fun i ↦ ⟨?_, ?_⟩
      · exact (this i).1
      · exact le_of_lt (this i).2
    · refine lt_of_lt_of_le hR₁ ?_
      exact Nat.le_ceil R

open scoped Pointwise

variable (c : ℝ) (s : Set (ι → ℝ))

abbrev IntegralPoints : Set (ι → ℝ) := s ∩ c⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))

variable (F : (ι → ℝ) → ℝ) (hF : Continuous F)

open scoped BigOperators

theorem Finite_integralPoints (hs₀ : IsBounded s) : Finite (IntegralPoints c s) := by
  rw [IntegralPoints, ← coe_pointwise_smul]
  by_cases hc : c = 0
  · rw [hc, inv_zero]
    rw [zero_smul]
    rw [zero_eq_bot, bot_coe]
    exact Finite.Set.finite_inter_of_right s {0}
  · rw [Zspan.smul _ (IsUnit.inv (Ne.isUnit hc))]
    refine Metric.finite_isBounded_inter_isClosed hs₀ ?_
    change IsClosed (span ℤ (Set.range (Basis.isUnitSMul (Pi.basisFun ℝ ι) _))).toAddSubgroup
    exact AddSubgroup.isClosed_of_discrete

def CountingFunction := Nat.card (IntegralPoints c s)

abbrev SeriesFunction := ∑' x : IntegralPoints c s, F x

theorem IntegralPointsEquiv :
    IntegralPoints c s ≃ (c • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := sorry

theorem CountingFunction_eq :
    CountingFunction c s =
      Nat.card (c • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := sorry

-- theorem IntegralPoints_mem_iff {x : ι → ℝ} :
--     x ∈ IntegralPoints s n ↔ (n:ℝ)⁻¹ • x ∈ IntegralPoints' ι s n := by
--   simp only [Set.mem_inter_iff, SetLike.mem_coe, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
--     not_false_eq_true, ← Set.mem_smul_set_iff_inv_smul_mem₀, smul_inv_smul₀]

-- def IntegralPointsEquiv : IntegralPoints ι s n ≃ IntegralPoints' ι s n := by
--   refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
--   · rintro ⟨x, hx⟩
--     exact ⟨(n:ℝ)⁻¹ • x, (IntegralPoints_mem_iff ι n s).mp hx⟩
--   · intro _ _ h
--     have := congr_arg ((n:ℝ) • ·) (Subtype.mk_eq_mk.mp h)
--     simpa [smul_inv_smul₀, SetCoe.ext_iff, this]
--   · rintro ⟨y, hy⟩
--     refine ⟨⟨((n:ℝ) • y), ?_⟩, ?_⟩
--     · simpa only [IntegralPoints_mem_iff, ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true,
--       inv_smul_smul₀]
--     · simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, inv_smul_smul₀]

-- theorem IntegralPointsEquiv_apply (x : IntegralPoints s n) :
--     (IntegralPointsEquiv ι n s x : ι → ℝ) = (n:ℝ)⁻¹ • x := rfl

-- theorem IntegralPointsEquiv_symm_apply (x : IntegralPoints' ι s n) :
--     ((IntegralPointsEquiv ι n s).symm x : ι → ℝ) = (n:ℝ) • x := by
--   have := IntegralPointsEquiv_apply ι n s ((IntegralPointsEquiv ι n s).symm x)
--   simp only [Equiv.apply_symm_apply] at this
--   rw [this]
--   simp

theorem UnitBoxTag_mem_smul_span (ν : ι → ℤ) :
    UnitBoxTag n ν ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
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
    UnitBoxTag n (UnitBoxIndex n x) = x := by
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

theorem UnitBoxIndex_injective_of_mem {x y : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (hy : y ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (h : UnitBoxIndex n x = UnitBoxIndex n y) : x = y := by
  have := congr_arg (UnitBoxTag n ·) h
  dsimp only at this
  rwa [UnitBoxTag_eq_of_mem_smul_span n hx, UnitBoxTag_eq_of_mem_smul_span n hy] at this

theorem UnitBoxTaggedPrepartition_tag_mem {x : ι → ℝ} {B : Box ι} (hB : HasIntegralVertices B)
    (hs₁ : s ≤ B) (hx : x ∈ IntegralPoints n s) :
    (UnitBoxTaggedPrepartition n B).tag (UnitBoxPart n (UnitBoxIndex n x)) ∈ s := by
  rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
  · exact hx.1
  · exact hx.2
  · refine UnixBoxIndexAdmissible_of_mem_box n hB ?_
    exact hs₁ hx.1

theorem SeriesFunction_eq {B : Box ι} (hB : HasIntegralVertices B) (hs₀ : s ≤ B) :
    ∑' x : IntegralPoints n s, F x =
      Finset.sum (UnitBoxTaggedPrepartition n B).toPrepartition.boxes
        fun C ↦ (Set.indicator s F ((UnitBoxTaggedPrepartition n B).tag C)) := by
  classical
  -- have : Fintype (IntegralPoints s n) := by
  --   have : Fintype ((n:ℝ) • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := sorry
  --   refine @Fintype.ofEquiv _ _ this ?_
  --   rw [IntegralPoints]

  --   refine Set.Finite.fintype ?_

  --   let T := (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))
  --   have : DiscreteTopology ((n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := by

  --     sorry
  --   refine Metric.finite_isBounded_inter_isClosed ?_ ?_
  --   -- refine Bornology.IsBounded.smul₀ ?_ _
  --   -- have := UnitBox_isBounded ι A
  --   refine Bornology.IsBounded.subset ?_ hs₁
  --   exact Box.IsBounded B

  --   -- change IsClosed (span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup
  --   -- exact AddSubgroup.isClosed_of_discrete
  have : IsBounded s := by
    refine IsBounded.subset ?_ hs₀
    exact Box.IsBounded B
  have := @Fintype.ofFinite _ (Finite_integralPoints n s this)
  rw [tsum_fintype]
  rw [Finset.sum_indicator_eq_sum_filter]
  have : (n:ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact PNat.ne_zero n
  rw [Finset.sum_set_coe (IntegralPoints n s)]
  refine Finset.sum_nbij ?_ ?_ ?_ ?_ ?_
  · exact fun x ↦ UnitBoxPart n (UnitBoxIndex n x)
  · simp_rw [Set.mem_toFinset, Finset.mem_filter]
    intro x hx
    -- have t1 := UnixBoxIndexAdmissible_of_mem_box n hB (hs₁ hx.1)
    rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition]
    · refine ⟨?_, ?_⟩
      · refine UnitBoxPart_index_mem _ hB ?_
        exact hs₀ hx.1
      · rw [UnitBoxTaggedPrepartition_tag_eq]
        rw [UnitBoxTag_eq_of_mem_smul_span]
        exact hx.1
        exact hx.2
        exact UnixBoxIndexAdmissible_of_mem_box n hB (hs₀ hx.1)
  · simp_rw [Set.coe_toFinset]
    intro x hx y hy h
    rw [(UnitBoxPart_injective n).eq_iff] at h
    exact UnitBoxIndex_injective_of_mem n hx.2 hy.2 h
  · intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq, BoxIntegral.Prepartition.mem_boxes,
      BoxIntegral.TaggedPrepartition.mem_toPrepartition, UnitBoxTaggedPrepartition_mem_iff] at hx
    obtain ⟨⟨ν, hν, rfl⟩, h⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · exact UnitBoxTag n ν
    · rw [Set.coe_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · rwa [UnitBoxTaggedPrepartition_tag_eq] at h
        exact hν
      · rw [← coe_pointwise_smul]
        exact UnitBoxTag_mem_smul_span n ν
    · simp
  · intro x hx
    rw [Set.mem_toFinset] at hx
    rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
    · exact hx.2
    · exact UnixBoxIndexAdmissible_of_mem_box n hB (hs₀ hx.1)

theorem UnitBoxTaggedPrepartition_integralSum' {B : Box ι} (hB : HasIntegralVertices B)
    (hs₀ : s ≤ B) :
    BoxIntegral.integralSum (Set.indicator s F)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
        (UnitBoxTaggedPrepartition n B) = (∑' x : IntegralPoints n s, F x) / n ^ card ι := by
  unfold BoxIntegral.integralSum
  rw [SeriesFunction_eq n s F hB hs₀, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hB
  rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
    UnitBoxTaggedPrepartition_mem_iff] at hB
  obtain ⟨_, _, rfl⟩ := hB
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, UnitBoxPart_volume,
    smul_eq_mul, mul_comm, ENNReal.toReal_div, ENNReal.one_toReal, ENNReal.toReal_pow,
    ENNReal.toReal_nat, mul_one_div]

theorem UnitBoxTaggedPrepartition_integralSum n {B : Box ι} (hB : HasIntegralVertices B)
    (hs₀ : s ≤ B) :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (UnitBoxTaggedPrepartition n B) = (CountingFunction n s : ℝ) / n ^ card ι := by
  convert UnitBoxTaggedPrepartition_integralSum' n s (fun _ ↦ (1:ℝ)) hB hs₀
  rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rfl

variable (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)

open Filter

theorem main'' :
    Tendsto (fun n : ℕ ↦ (∑' x : IntegralPoints n s, F x) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt hs₁ 0 0
  have : ContinuousOn (Set.indicator s (fun x ↦ F x)) (BoxIntegral.Box.Icc B) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this
    BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in B, Set.indicator s F x = ∫ x in s, F x := by
    rw [MeasureTheory.integral_indicator hs₂]
    rw [Measure.restrict_restrict_of_subset hs₀]
  rw [this] at main

  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main (eps / 2) (half_pos h_eps)
  obtain ⟨r, hr₁, hr₂⟩ := main
  specialize hr₁ 0 rfl -- this say that ∀ x, r x = r 0
  specialize hr₂ 0
  let N : ℕ+ := by
    refine ⟨?_, ?_⟩
    exact Nat.ceil (1 / (r 0 0 : ℝ))
    rw [Nat.ceil_pos, one_div, inv_pos]
    exact (r 0 0).mem
  use N
  intro n hn
  have : ∀ n, N ≤ n →
      BoxIntegral.IntegrationParams.MemBaseSet BoxIntegral.IntegrationParams.Riemann
        B 0 (r 0) (UnitBoxTaggedPrepartition n B) := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 0 = fun _ ↦ r 0 0 := Function.funext_iff.mpr hr₁
      rw [this]
      refine UnitBoxTaggedPrepartition_isSubordinate _ _ _ ?_
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock _ _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
  have hn₀ : 0 < n := lt_of_lt_of_le N.prop hn
  specialize hr₂ _ (this ⟨n, hn₀⟩ hn) (UnitBoxTaggedPrepartition_isPartition ⟨n, hn₀⟩ hB)
  rw [UnitBoxTaggedPrepartition_integralSum'] at hr₂
  refine lt_of_le_of_lt hr₂ ?_
  exact half_lt_self_iff.mpr h_eps
  exact hB
  exact hs₀

theorem main' :
    Tendsto (fun n : ℕ ↦ (CountingFunction n s : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  convert main'' s (fun _ ↦ 1) hs₁ hs₂
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl
  · rw [set_integral_const, smul_eq_mul, mul_one]

variable (h₃ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s)

theorem CountingFunction_mono {x y : ℝ} (h₁ : 0 < x) (h₂ : x ≤ y) :
    CountingFunction x s ≤ CountingFunction y s := by
  -- IntegralPointsEquiv
  rw [CountingFunction_eq, CountingFunction_eq]
  refine Nat.card_mono ?_ ?_
  · sorry
    -- exact Fintype_integralPoints c s hs₁
  · intro x hx
    refine ⟨?_, ?_⟩
    · exact h₃ h₁ h₂ hx.1
    · exact hx.2

theorem main :
    Tendsto (fun x : ℝ ↦ (CountingFunction x s : ℝ) / x ^ card ι)
      atTop (nhds (volume s).toReal) := by
  -- Make a bunch of ∀ᶠ x in atTop for filter_upwards?
  have i₁ : ∀ᶠ x : ℝ in atTop, (CountingFunction (Nat.floor x) s : ℝ) / (Nat.ceil x) ^ card ι ≤
      (CountingFunction x s : ℝ) / x ^ card ι := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    gcongr
    refine CountingFunction_mono s h₃ ?_ ?_
    · rwa [Nat.cast_pos, Nat.floor_pos]
    · exact Nat.floor_le (le_trans zero_le_one hx)
    · exact Nat.le_ceil _
  have i₂ : ∀ᶠ x : ℝ in atTop, (CountingFunction x s : ℝ) / x ^ card ι ≤
      (CountingFunction (Nat.ceil x) s : ℝ) / (Nat.floor x) ^ card ι := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    gcongr
    refine pow_pos ?_ _
    exact Nat.cast_pos.mpr (Nat.floor_pos.mpr hx)
    refine CountingFunction_mono s h₃ ?_ ?_
    · linarith
    · exact Nat.le_ceil _
    · refine Nat.floor_le ?_
      exact le_trans zero_le_one hx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ i₁ i₂
  · have : (fun x : ℝ ↦ (CountingFunction (Nat.floor x) s : ℝ) / (Nat.floor x) ^ card ι *
        (Nat.floor x / Nat.ceil x ) ^ card ι) =ᶠ[atTop]
        fun x : ℝ ↦ (CountingFunction (Nat.floor x) s) / (Nat.ceil x) ^ card ι := by
      filter_upwards [eventually_ge_atTop 1] with _ _
      rw [mul_comm_div, ← div_pow, div_div, div_mul_cancel_right₀, inv_pow, div_eq_mul_inv]
      rwa [Nat.cast_ne_zero, Nat.ne_zero_iff_zero_lt, Nat.floor_pos]
    rw [show (volume s).toReal = (volume s).toReal * 1 ^ card ι by ring]
    refine Tendsto.congr' this ?_
    refine Tendsto.mul ?_ ?_
    · exact Tendsto.comp (main' s hs₁ hs₂) tendsto_natFloor_atTop
    · refine Tendsto.pow ?_ _
      convert Tendsto.inv₀ (tendsto_nat_ceil_div_floor_atTop (R := ℝ)) one_ne_zero using 2
      · rw [inv_div]
      · rw [inv_one]
  · have : (fun x : ℝ ↦ (CountingFunction (Nat.ceil x) s : ℝ) / (Nat.ceil x) ^ card ι *
        (Nat.ceil x / Nat.floor x ) ^ card ι) =ᶠ[atTop]
        fun x : ℝ ↦ (CountingFunction (Nat.ceil x) s) / (Nat.floor x) ^ card ι := by
      filter_upwards [eventually_gt_atTop 0] with _ _
      rw [mul_comm_div, ← div_pow, div_div, div_mul_cancel_right₀, inv_pow, div_eq_mul_inv]
      rwa [Nat.cast_ne_zero, Nat.ne_zero_iff_zero_lt, Nat.ceil_pos]
    rw [show (volume s).toReal = (volume s).toReal * 1 ^ card ι by ring]
    refine Tendsto.congr' this ?_
    refine Tendsto.mul ?_ ?_
    · exact Tendsto.comp (main' s hs₁ hs₂) tendsto_natCeil_atTop
    · refine Tendsto.pow ?_ _
      exact tendsto_nat_ceil_div_floor_atTop

end BoxIntegral
