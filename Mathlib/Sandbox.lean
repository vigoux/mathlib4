import Mathlib

noncomputable section

open MeasureTheory Submodule Filter Fintype

open scoped Pointwise ENNReal Classical

variable (ι : Type*)

variable {r : ℕ+}

def UnitBox : BoxIntegral.Box ι where
  lower := fun _ ↦ 0
  upper := fun _ ↦ 1
  lower_lt_upper := fun _ ↦ by norm_num

def UnitBoxTag (ν : ι → Fin r) : ι → ℝ := fun i ↦ ν i / r

def UnitBoxPart (ν : ι → Fin r) : BoxIntegral.Box ι where
  lower := fun i ↦ UnitBoxTag ι ν i
  upper := fun i ↦ UnitBoxTag ι ν i + 1 / r
  lower_lt_upper := fun _ ↦ by norm_num

theorem UnitBoxPart_le_UnitBox (ν : ι → Fin r) : UnitBoxPart ι ν ≤ UnitBox ι := sorry

variable [Fintype ι]

def UnitBoxPrepartition : BoxIntegral.TaggedPrepartition (UnitBox ι) where
  boxes := Finset.univ.image (fun ν : ι → Fin r ↦ UnitBoxPart ι ν)
  le_of_mem' _ hJ := by
    obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hJ
    exact UnitBoxPart_le_UnitBox ι ν
  pairwiseDisjoint := sorry
  tag := by
    intro J
    by_cases hJ : ∃ ν : ι → Fin r, J = UnitBoxPart ι ν
    · exact UnitBoxTag ι hJ.choose
    · exact 0
  tag_mem_Icc := sorry

variable {ι} (r)

variable (s : Set (ι → ℝ))

def CountingFunction (r : ℕ) :=
  if r = 0 then 0 else
    Nat.card ((r:ℝ) • s ∩ span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))

example :
    Tendsto (fun r : ℕ ↦ (CountingFunction s r : ℝ) / r ^ card ι)
      atTop (nhds (volume s).toReal) := by
  have : ContinuousOn (Set.indicator s (fun _ ↦ (1:ℝ))) (BoxIntegral.Box.Icc (UnitBox ι)) := sorry
  have main := IntegrableOn.hasBoxIntegral' this BoxIntegral.IntegrationParams.Riemann
  rw [BoxIntegral.hasIntegral_iff] at main
  have : ∫ x in (UnitBox ι), Set.indicator s (fun x ↦ (1:ℝ)) x = (volume s).toReal := by sorry
  rw [this] at main
  rw [Metric.tendsto_atTop]
  intro eps h_eps
  specialize main eps h_eps
  obtain ⟨r, hr₁, hr₂⟩ := main
  specialize hr₁ 1
  specialize hr₂ 1

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
