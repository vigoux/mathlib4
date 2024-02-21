import Mathlib

section analysis

open Filter BigOperators Topology

example :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n:ℂ) ^ s)
      (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
  have : Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
    refine Filter.Tendsto.mono_left riemannZeta_residue_one ?_
    refine nhdsWithin_mono _ ?_
    aesop
  refine Tendsto.congr' ?_ this
  rw [eventuallyEq_nhdsWithin_iff]
  refine eventually_of_forall (fun s hs ↦ ?_)
  exact congr_arg ((s - 1) * ·) (zeta_eq_tsum_one_div_nat_cpow hs)

example {x : ℕ → ℝ} (h₁ : Monotone x) {l : ℝ}
    (h₂ : Tendsto x atTop ⊤)
    (h₃ : Tendsto (fun c : ℝ ↦ Nat.card {i | x i ≤ c} / c) atTop (nhds l)) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' i, (x i) ^ (- s)) (nhdsWithin 1 {1}ᶜ) (nhds l) := by
  have t1 : ∀ k, Nat.card {i | x i ≤ x k} = k + 1 := sorry
  have t2 : Tendsto (fun k ↦ (k + 1) / x k) atTop (nhds l) := by
    rw [Metric.tendsto_atTop] at h₃ ⊢
    intro ε hε
    specialize h₃ ε hε
    obtain ⟨B, hB⟩ := h₃
    have : ∃ N, ∀ n ≥ N, B ≤ x n := by
      exact?

  sorry

end analysis

section Box

theorem BoxIntegral.Box.IsBounded_Icc {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded (BoxIntegral.Box.Icc B) := B.isCompact_Icc.isBounded

theorem BoxIntegral.Box.IsBounded {ι : Type*} [Fintype ι] (B : BoxIntegral.Box ι) :
    Bornology.IsBounded B.toSet :=
  Bornology.IsBounded.subset (BoxIntegral.Box.IsBounded_Icc B) coe_subset_Icc

end Box

noncomputable section

namespace BoxIntegral

open Bornology MeasureTheory Fintype

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
    add_sub_cancel, ← _root_.le_div_iff' h_npos, ← div_lt_iff' h_npos, add_div]

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
  rw [Real.ediam_Icc, UnitBoxPart, add_sub_cancel', ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one]
  exact Nat.cast_pos.mpr n.pos

@[simp]
theorem UnitBoxPart_volume (ν : ι → ℤ) :
    volume (UnitBoxPart n ν : Set (ι → ℝ)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc, UnitBoxPart,
    add_sub_cancel']
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.pos), ENNReal.ofReal_one,
    ENNReal.ofReal_coe_nat, Finset.card_univ, one_div, one_div, ENNReal.inv_pow]

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
  let A := { ν : ι → ℤ | UnitBoxPart n ν ≤ B}
  refine Set.Finite.toFinset (s := A) ?_
  refine UnitBoxIndex_setFinite_of_finite_measure n ?_ ?_
  · exact B.measurableSet_coe.nullMeasurableSet
  · rw [← lt_top_iff_ne_top]
    refine IsBounded.measure_lt_top ?_
    exact Box.IsBounded B

theorem UnitBoxIndex_mem_admissible (B : Box ι) (ν : ι → ℤ) :
    ν ∈ UnitBoxIndexAdmissible n B ↔ UnitBoxPart n ν ≤ B := by
  rw [UnitBoxIndexAdmissible, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

open Classical in
def UnitBoxTaggedPrepartition (B : Box ι) : BoxIntegral.TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ UnitBoxPart n ν) (UnitBoxIndexAdmissible n B)
  le_of_mem' _ hB := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hB
    exact (UnitBoxIndex_mem_admissible n B _).mp hν
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
      rw [UnitBoxIndex_mem_admissible] at this
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

def IsThick_at (B : Box ι) : Prop :=
  ∀ x : ι → ℝ, x ∈ B → UnitBoxPart n (UnitBoxIndex n x) ≤ B

def IsThick (B : Box ι) : Prop := ∀ n, IsThick_at n B

theorem UnitBoxTaggedPrepartition_isPartition {B : Box ι} (hB : IsThick_at n B) :
    (UnitBoxTaggedPrepartition n B).IsPartition := by
  intro x hx
  use UnitBoxPart n (UnitBoxIndex n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, UnitBoxTaggedPrepartition_mem_iff]
    refine ⟨UnitBoxIndex n x, ?_, rfl⟩
    rw [UnitBoxIndex_mem_admissible]
    exact hB x hx
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


#exit

/-- A `BoxIntegral` is integral if its vertices are integers. -/
class IsIntegral {ι : Type*} (B : BoxIntegral.Box ι) : Prop where
  isIntegral : ∃ (lw : ι → ℤ) (up : ι → ℤ), ∀ i, B.lower i = lw i ∧ B.upper i = up i

theorem le_isIntegral_of_isBounded {ι : Type*} [Finite ι] {s : Set (ι → ℝ)} (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, IsIntegral B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt h 0 0
  let C : ℕ+ := ⟨Nat.ceil R, Nat.ceil_pos.mpr hR₁⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine BoxIntegral.Box.mk (fun _ ↦ - C) (fun _ ↦ C ) ?_
    intro i
    norm_num [hR₁]
  · exact fun _ ↦ - C
  · exact fun _ ↦ C
  · intro _
    simp
  · sorry

#exit

set_option autoImplicit false

noncomputable section pi

open MeasureTheory Submodule Filter Fintype

open scoped Pointwise NNReal ENNReal

variable (ι : Type*) (A : ℕ+)

def UnitBox : BoxIntegral.Box ι where
  lower := fun _ ↦ -(A:ℝ)
  upper := fun _ ↦ (A:ℝ)
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBox_mem (x : ι → ℝ) : x ∈ UnitBox ι A ↔ ∀ i, - A < x i ∧ x i ≤ A := by
  simp_rw [BoxIntegral.Box.mem_def, UnitBox, Set.mem_Ioc]

theorem UnitBox_ball_le [Fintype ι] :
    Metric.ball 0 A ⊆ (UnitBox ι A).toSet := by
  simp_rw [ball_pi _ (Nat.cast_pos.mpr A.pos), BoxIntegral.Box.coe_eq_pi,
    Set.univ_pi_subset_univ_pi_iff, Real.ball_eq_Ioo, UnitBox, Pi.zero_apply, zero_sub, zero_add,
    Set.Ioo_subset_Ioc_self, implies_true, true_or]

theorem UnitBox_le_closedBall [Fintype ι] :
    (UnitBox ι A).toSet ⊆ Metric.closedBall 0 A := by
  simp_rw [closedBall_pi _ (Nat.cast_nonneg A), BoxIntegral.Box.coe_eq_pi,
    Set.univ_pi_subset_univ_pi_iff, Real.closedBall_eq_Icc, UnitBox, Pi.zero_apply, zero_sub,
    zero_add, Set.Ioc_subset_Icc_self, implies_true, true_or]

theorem UnitBox_isBounded [Finite ι] :
    Bornology.IsBounded (UnitBox ι A).toSet :=
  have := Fintype.ofFinite ι
  (Metric.isBounded_iff_subset_closedBall _).mpr ⟨_, UnitBox_le_closedBall ι A⟩

variable (n : ℕ+)

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

variable [Fintype ι] [DecidableEq ι] -- Use Finite instead so Decidable should not be necessary

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

@[simp]
theorem UnitBoxPart_volume (ν : ι → ℤ) :
    (volume (UnitBoxPart ι n ν : Set (ι → ℝ))).toReal = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc]
  simp_rw [UnitBoxPart, add_sub_cancel']
  rw [Finset.prod_const, ENNReal.ofReal_div_of_pos, ENNReal.toReal_pow, ENNReal.toReal_div,
    div_pow, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, one_pow, Fintype.card]
  any_goals positivity
  exact Nat.cast_pos.mpr n.pos

def AdmissibleIndex :
  Finset (ι → ℤ) := Fintype.piFinset (fun _ ↦ Finset.Ico (n * - (A:ℤ)) (n * A))

variable {ι A n} in
@[simp]
theorem UnitBoxIndex_admissible_iff {x : ι → ℝ} :
    UnitBoxIndex ι n x ∈ AdmissibleIndex ι A n ↔ x ∈ UnitBox ι A := by
  have h₁ : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  have h₂ : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  simp_rw [UnitBox_mem, AdmissibleIndex, mem_piFinset, Finset.mem_Ico, UnitBoxIndex_apply,
    Int.lt_iff_add_one_le, sub_add_cancel, le_sub_iff_add_le, ← Int.lt_iff_add_one_le, Int.lt_ceil,
    Int.ceil_le,  ← le_div_iff' h₁, ← div_lt_iff' h₁,  Int.cast_mul, mul_div_assoc,
    Int.cast_neg, Int.cast_ofNat, mul_div_cancel' _ h₂]

variable {ι A n} in
theorem UnitBoxPart_le_UnitBox {ν : ι → ℤ} :
    UnitBoxPart ι n ν ≤ UnitBox ι A ↔ ν ∈ AdmissibleIndex ι A n := by
  have h : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  simp_rw [BoxIntegral.Box.le_iff_bounds, UnitBox, UnitBoxPart, AdmissibleIndex, mem_piFinset,
    Finset.mem_Ico, Pi.le_def, ← forall_and, ← add_div, le_div_iff' h, div_le_iff' h,
    Int.lt_iff_add_one_le, ← Int.cast_le (α := ℝ), Int.cast_mul, Int.cast_add, Int.cast_one,
    Int.cast_neg, Int.cast_ofNat]

variable [DecidableEq (BoxIntegral.Box ι)]

def UnitBoxTaggedPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι A) where
  boxes := Finset.image (fun ν ↦ UnitBoxPart ι n ν) (AdmissibleIndex ι A n)
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
    by_cases hB : ∃ ν ∈ AdmissibleIndex ι A n, B = UnitBoxPart ι n ν
    · exact UnitBoxTag ι n hB.choose
    · exact 1
  tag_mem_Icc := by
    intro B
    split_ifs with h
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe]
      have t2 := UnitBoxPart_le_UnitBox.mpr h.choose_spec.1
      refine t2 ?_
      exact UnitBoxTag_mem_unitBoxPart ι n (Exists.choose h)
    · refine BoxIntegral.Box.coe_subset_Icc ?_
      rw [BoxIntegral.Box.mem_coe, UnitBox_mem]
      intro _
      simp
      refine ⟨?_, ?_⟩
      linarith
      exact A.pos

variable {ι A n} in
@[simp]
theorem mem_UnitBoxTaggedPrepartition_iff {B : BoxIntegral.Box ι} :
    B ∈ UnitBoxTaggedPrepartition ι A n ↔
      ∃ ν ∈ AdmissibleIndex ι A n, UnitBoxPart ι n ν = B := by simp [UnitBoxTaggedPrepartition]

theorem UnitBoxPart_index_mem {x : ι → ℝ} (hx : x ∈ UnitBox ι A) :
    UnitBoxPart ι n (UnitBoxIndex ι n x) ∈ UnitBoxTaggedPrepartition ι A n := by
  rw [mem_UnitBoxTaggedPrepartition_iff]
  refine ⟨UnitBoxIndex ι n x, ?_, rfl⟩
  rw [UnitBoxIndex_admissible_iff]
  exact hx

@[simp]
theorem UnitBoxTaggedPrepartition_tag_eq {ν : ι → ℤ} (hν : ν ∈ AdmissibleIndex ι A n) :
    (UnitBoxTaggedPrepartition ι A n).tag (UnitBoxPart ι n ν) = UnitBoxTag ι n ν := by
  dsimp only [UnitBoxTaggedPrepartition]
  have h : ∃ ν' ∈ AdmissibleIndex ι A n, UnitBoxPart ι n ν = UnitBoxPart ι n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (UnitBoxTag_injective ι n).eq_iff, ← (UnitBoxPart_injective ι n).eq_iff]
  exact h.choose_spec.2.symm

theorem UnitBoxTaggedPrepartition_isHenstock :
    (UnitBoxTaggedPrepartition ι A n).IsHenstock := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  rw [UnitBoxTaggedPrepartition_tag_eq ι A n hν]
  exact BoxIntegral.Box.coe_subset_Icc (UnitBoxTag_mem_unitBoxPart ι n ν)

theorem UnitBoxTaggedPrepartition_isPartition :
    (UnitBoxTaggedPrepartition ι A n).IsPartition := by
  intro x hx
  use UnitBoxPart ι n (UnitBoxIndex ι n x)
  refine ⟨?_, ?_⟩
  · rw [BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition_iff]
    exact ⟨UnitBoxIndex ι n x, UnitBoxIndex_admissible_iff.mpr hx, rfl⟩
  · exact (UnitBoxPart_mem_iff_index_eq ι n).mpr rfl

theorem UnitBoxTaggedPrepartition_isSubordinate {r : ℝ} (hr : 0 < r) (hn : 1 / r ≤ n) :
    (UnitBoxTaggedPrepartition ι A n).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hB
  obtain ⟨ν, hν, rfl⟩ := mem_UnitBoxTaggedPrepartition_iff.mp hB
  dsimp
  have t1 : Metric.diam (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) ≤ r := by
    refine le_trans (UnitBoxPart_diam ι n ν) ?_
    rw [div_le_iff]
    rwa [div_le_iff hr, mul_comm] at hn
    exact Nat.cast_pos.mpr n.pos
  intro x hx
  rw [Metric.mem_closedBall, UnitBoxTaggedPrepartition_tag_eq ι A n hν]
  have t2 : UnitBoxTag ι n ν ∈ (BoxIntegral.Box.Icc (UnitBoxPart ι n ν)) := by
    refine BoxIntegral.Box.coe_subset_Icc ?_
    exact UnitBoxTag_mem_unitBoxPart _ _ _
  have t3 := Metric.dist_le_diam_of_mem ?_ hx t2
  exact le_trans t3 t1
  refine IsCompact.isBounded ?_
  exact BoxIntegral.Box.isCompact_Icc (UnitBoxPart ι n ν)

variable (s : Set (ι → ℝ))

abbrev IntegralPoints (c : ℝ) : Set (ι → ℝ) := c • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι))

-- Only keep this version and just prove the equiv with the other one
abbrev IntegralPoints' (c : ℝ) : Set (ι → ℝ) := s ∩ c⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))

variable (F : (ι → ℝ) → ℝ) (hF : Continuous F)

open scoped BigOperators

-- Define c before so that arguments are always in the same order
def CountingFunction (c : ℝ) := Nat.card (IntegralPoints ι s c)

-- Probably inline that instead
abbrev SeriesFunction (c : ℝ) := ∑' x : IntegralPoints ι s c, F x

theorem IntegralPoints_mem_iff {x : ι → ℝ} :
    x ∈ IntegralPoints ι s n ↔ (n:ℝ)⁻¹ • x ∈ IntegralPoints' ι s n := by
  simp only [Set.mem_inter_iff, SetLike.mem_coe, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
    not_false_eq_true, ← Set.mem_smul_set_iff_inv_smul_mem₀, smul_inv_smul₀]

def IntegralPointsEquiv : IntegralPoints ι s n ≃ IntegralPoints' ι s n := by
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ⟨(n:ℝ)⁻¹ • x, (IntegralPoints_mem_iff ι n s).mp hx⟩
  · intro _ _ h
    have := congr_arg ((n:ℝ) • ·) (Subtype.mk_eq_mk.mp h)
    simpa [smul_inv_smul₀, SetCoe.ext_iff, this]
  · rintro ⟨y, hy⟩
    refine ⟨⟨((n:ℝ) • y), ?_⟩, ?_⟩
    · simpa only [IntegralPoints_mem_iff, ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true,
      inv_smul_smul₀]
    · simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, inv_smul_smul₀]

theorem IntegralPointsEquiv_apply (x : IntegralPoints ι s n) :
    (IntegralPointsEquiv ι n s x : ι → ℝ) = (n:ℝ)⁻¹ • x := rfl

theorem IntegralPointsEquiv_symm_apply (x : IntegralPoints' ι s n) :
    ((IntegralPointsEquiv ι n s).symm x : ι → ℝ) = (n:ℝ) • x := by
  have := IntegralPointsEquiv_apply ι n s ((IntegralPointsEquiv ι n s).symm x)
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp

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

theorem UnitBoxIndex_injective_of_mem {x y : ι → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (hy : y ∈ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (h : UnitBoxIndex ι n x = UnitBoxIndex ι n y) : x = y := by
  have := congr_arg (UnitBoxTag ι n ·) h
  dsimp only at this
  rwa [UnitBoxTag_eq_of_mem_smul_span ι n hx, UnitBoxTag_eq_of_mem_smul_span ι n hy] at this

theorem UnitBoxTaggedPrepartition_tag_mem {x : ι → ℝ} (hs₁ : s ≤ UnitBox ι A)
    (hx : x ∈ IntegralPoints' ι s n) :
    (UnitBoxTaggedPrepartition ι A n).tag (UnitBoxPart ι n (UnitBoxIndex ι n x)) ∈ s := by
  rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
  exact hx.1
  exact hx.2
  rw [UnitBoxIndex_admissible_iff]
  exact hs₁ hx.1

-- variable (hs₁ : s ≤ UnitBox ι H)

-- theorem Index_admissible_of_mem0 {x : ι → ℝ} (hx : x ∈ IntegralPoints' ι s n) :
--     UnitBoxIndex ι n x ∈ AdmissibleIndex ι lw up n := by
--   rw [← @UnitBox_mem_iff_index]
--   refine hs₁ (Set.mem_of_mem_inter_left hx)

theorem SeriesFunction_eq (hs₁ : s ≤ UnitBox ι A) :
    ∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x) =
      Finset.sum (UnitBoxTaggedPrepartition ι A n).toPrepartition.boxes
        fun B ↦ (Set.indicator s F ((UnitBoxTaggedPrepartition ι A n).tag B)) := by
  classical
  simp_rw [← Equiv.tsum_eq (IntegralPointsEquiv ι n s).symm, IntegralPointsEquiv_symm_apply]
  have : Fintype (IntegralPoints' ι s n) := by
    convert Fintype.ofEquiv (IntegralPoints ι s n) (IntegralPointsEquiv ι n s)
    rw [IntegralPoints]
    refine Set.Finite.fintype ?_
    refine Metric.finite_isBounded_inter_isClosed ?_ ?_
    refine Bornology.IsBounded.smul₀ ?_ _
    have := UnitBox_isBounded ι A
    exact Bornology.IsBounded.subset this hs₁
    change IsClosed (span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup
    exact AddSubgroup.isClosed_of_discrete
  rw [tsum_fintype]
  rw [Finset.sum_indicator_eq_sum_filter]
  have : (n:ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact PNat.ne_zero n
  simp_rw [inv_smul_smul₀ this]
  rw [Finset.sum_set_coe (IntegralPoints' ι s n)]
  refine Finset.sum_nbij ?_ ?_ ?_ ?_ ?_
  · exact fun x ↦ UnitBoxPart ι n (UnitBoxIndex ι n x)
  · simp_rw [Set.mem_toFinset, Finset.mem_filter]
    intro x hx
    rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition]
    · refine ⟨?_, ?_⟩
      · refine UnitBoxPart_index_mem ι A n ?_
        exact hs₁ hx.1
      · exact UnitBoxTaggedPrepartition_tag_mem ι A n s hs₁ hx
  · simp_rw [Set.coe_toFinset]
    intro x hx y hy h
    rw [(UnitBoxPart_injective ι n).eq_iff] at h
    exact UnitBoxIndex_injective_of_mem ι n hx.2 hy.2 h
  · intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq, BoxIntegral.Prepartition.mem_boxes,
      BoxIntegral.TaggedPrepartition.mem_toPrepartition, mem_UnitBoxTaggedPrepartition_iff] at hx
    obtain ⟨⟨ν, hν, rfl⟩, h⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · exact UnitBoxTag ι n ν
    · rw [Set.coe_toFinset, Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · rwa [UnitBoxTaggedPrepartition_tag_eq ι A n hν] at h
      · rw [← coe_pointwise_smul]
        exact UnitBoxTag_mem_smul_span ι n ν
    · simp
  · intro x hx
    rw [Set.mem_toFinset] at hx
    rw [UnitBoxTaggedPrepartition_tag_eq, UnitBoxTag_eq_of_mem_smul_span]
    · exact hx.2
    · rw [UnitBoxIndex_admissible_iff]
      exact hs₁ hx.1

theorem UnitBoxTaggedPrepartition_integralSum' (hs₁ : s ≤ UnitBox ι A) :
    BoxIntegral.integralSum (Set.indicator s F)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
        (UnitBoxTaggedPrepartition ι A n) = (
        ∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x)) / n ^ card ι := by
  unfold BoxIntegral.integralSum
  rw [SeriesFunction_eq ι A n s F hs₁, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro _ hB
  rw [BoxIntegral.Prepartition.mem_boxes, BoxIntegral.TaggedPrepartition.mem_toPrepartition,
    mem_UnitBoxTaggedPrepartition_iff] at hB
  obtain ⟨_, _, rfl⟩ := hB
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply, UnitBoxPart_volume,
    smul_eq_mul, mul_comm, mul_one_div]

theorem UnitBoxTaggedPrepartition_integralSum n (hs₁ : s ≤ UnitBox ι A) :
    BoxIntegral.integralSum (Set.indicator s fun x ↦ 1)
      (BoxIntegral.BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (UnitBoxTaggedPrepartition ι A n) = (CountingFunction ι s n : ℝ) / n ^ card ι := by
  convert UnitBoxTaggedPrepartition_integralSum' ι A n s (fun _ ↦ (1:ℝ)) hs₁
  rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rfl

variable (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)

theorem main' :
    Tendsto (fun n : ℕ+ ↦ (∑' x : IntegralPoints ι s n, F ((n:ℝ)⁻¹ • x)) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨R, hR₁, hR₂⟩ := Bornology.IsBounded.subset_ball_lt hs₁ 0 0
  let C : ℕ+ := ⟨Nat.ceil R, Nat.ceil_pos.mpr hR₁⟩
  have hs : s ≤ UnitBox ι C := by
    have := UnitBox_ball_le ι C
    refine le_trans ?_ this
    refine le_trans hR₂ (Metric.ball_subset_ball ?_)
    exact Nat.le_ceil _
  have : ContinuousOn (Set.indicator s (fun x ↦ F x)) (BoxIntegral.Box.Icc (UnitBox ι C)) := sorry
  have main := ContinuousOn.hasBoxIntegral (volume : Measure (ι → ℝ)) this
    BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in (UnitBox ι C), Set.indicator s F x = ∫ x in s, F x := by
    rw [MeasureTheory.integral_indicator hs₂]
    rw [Measure.restrict_restrict_of_subset hs]
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
        (UnitBox ι C) 0 (r 0) (UnitBoxTaggedPrepartition ι C n) := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : r 0 = fun _ ↦ r 0 0 := Function.funext_iff.mpr hr₁
      rw [this]
      refine UnitBoxTaggedPrepartition_isSubordinate ι _ _ _ ?_
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
      exact UnitBoxTaggedPrepartition_isHenstock ι _ _
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h
    · intro h
      simp [BoxIntegral.IntegrationParams.Riemann] at h

  specialize hr₂ _ (this n hn) (UnitBoxTaggedPrepartition_isPartition ι C n)
  rw [UnitBoxTaggedPrepartition_integralSum'] at hr₂
  refine lt_of_le_of_lt hr₂ ?_
  exact half_lt_self_iff.mpr h_eps
  exact hs

theorem main :
    Tendsto (fun n : ℕ+ ↦ (CountingFunction ι s n : ℝ) / n ^ card ι)
      atTop (nhds (volume s).toReal) := by
  convert main' ι s (fun _ ↦ 1) hs₁ hs₂
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl
  · rw [set_integral_const, smul_eq_mul, mul_one]

end pi

noncomputable section general

open MeasureTheory MeasureTheory.Measure Submodule Filter Fintype

open scoped Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (s : Set E)

abbrev LatticePoints (c : ℝ) : Set E := c • s ∩ span ℤ (Set.range b)

abbrev LatticePoints' (c : ℝ) : Set E := s ∩ c⁻¹ • span ℤ (Set.range b)

def LatticeCountingFunction (c : ℝ) := Nat.card (LatticePoints b s c)

variable [Fintype ι]

def EquivIntegralPoints {c : ℝ} (hc : c ≠ 0) : LatticePoints' b s c ≃ IntegralPoints' ι (b.equivFun '' s) c := by
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · exact ⟨_, hx.1, rfl⟩
    · -- rw [← coe_pointwise_smul]
      refine ⟨c • b.equivFun x, ?_, ?_⟩
      · rw [SetLike.mem_coe]
        simp_rw [Basis.mem_span_iff_repr_mem, Basis.equivFun_apply,
          Pi.basisFun_repr, Set.mem_range, Pi.smul_apply, smul_eq_mul]
        intro i
        refine ⟨?_, ?_⟩

        sorry
      · simp [inv_smul_smul₀ hc]



theorem toto (c : ℝ) : LatticeCountingFunction b s c = CountingFunction ι (b.equivFun '' s) c := by
  refine Nat.card_congr ?_
  refine Set.BijOn.equiv b.equivFun ?_
  refine (Equiv.image_eq_iff_bijOn b.equivFun.toEquiv).mp ?_
  ext
  rw [LinearEquiv.coe_toEquiv, Set.InjOn.image_inter ((Basis.equivFun b).injective.injOn  _)
    (Set.subset_univ _) (Set.subset_univ _), Set.mem_inter_iff, Set.mem_inter_iff]
  erw [← Submodule.map_coe (b.equivFun.restrictScalars ℤ)]
  simp_rw [image_smul_set, Submodule.map_span, LinearEquiv.restrictScalars_apply, ← Set.range_comp]
  congr!
  ext
  rw [Function.comp_apply, Basis.equivFun_apply, Basis.repr_self]
  rfl

variable [MeasurableSpace E] [BorelSpace E]

variable [DecidableEq ι] [DecidableEq (BoxIntegral.Box ι)]

theorem main2 (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ+ ↦ (LatticeCountingFunction b s n : ℝ) / n ^ card ι)
      atTop (nhds (volume (b.equivFun '' s)).toReal) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fintype_basis b
  simp_rw [toto]
  convert main ι _ ?_ ?_
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    have := Bornology.IsVonNBounded.image (E := E) (F := ι → ℝ) (σ := RingHom.id ℝ) hs₁
    erw [← LinearMap.coe_toContinuousLinearMap']
    exact this _
  · rw [LinearEquiv.image_eq_preimage]
    have : Continuous b.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    have : Measurable b.equivFun.symm := by
      exact Continuous.measurable this
    exact this hs₂

variable (b₀ : Basis ι ℝ (ι → ℝ)) (s₀ : Set (ι → ℝ)) (hs₀₁ : Bornology.IsBounded s₀)
  (hs₀₂ : MeasurableSet s₀)

theorem main3 :
    Tendsto (fun n : ℕ+ ↦ (LatticeCountingFunction b₀ s₀ n : ℝ) / n ^ card ι)
      atTop (nhds (|(LinearEquiv.det b₀.equivFun : ℝ)| * (volume s₀).toReal)) := by
  convert main2 b₀ s₀ hs₀₁ hs₀₂ using 2
  rw [LinearEquiv.image_eq_preimage]
  rw [← MeasureTheory.Measure.map_apply₀]
  · erw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
    · rw [LinearEquiv.det_coe_symm, inv_inv]
      simp only [LinearEquiv.coe_det, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_mul, abs_nonneg, ENNReal.toReal_ofReal]
    · refine IsUnit.ne_zero ?_
      exact LinearEquiv.isUnit_det' _
  · have : Continuous b₀.equivFun.symm := by
      exact LinearMap.continuous_of_finiteDimensional _
    exact Continuous.aemeasurable this
  · exact MeasurableSet.nullMeasurableSet hs₀₂

end general
