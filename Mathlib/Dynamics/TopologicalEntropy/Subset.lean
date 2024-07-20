/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure
Proof that the topological entropy depends monotonically on the subset. Main results
are `entropy_monotone_space₁`/`entropy'_monotone_space₁` (for the cover version)
and `entropy_monotone_space₂`/`entropy'_monotone_space₂` (for the net version). I have decided
to keep all the intermediate steps, since they may be useful in the study of other systems.

For uniformly continuous maps, proof that the entropy of a subset is the entropy of its closure.
Main results are `entropy_of_closure` and `entropy'_of_closure`.

TODO: I think one could implement a notion of Hausdorff onvergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of these lemmas on closures.
-/

namespace Entropy

open CoverEntropy EReal ENNReal NetEntropy Set

variable {X : Type*}

/-! ### Monotonicity of entropy as a function of the subset -/

theorem dyncover_monotone_space {T : X → X} {F G : Set X} (F_G : F ⊆ G) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynamicalCoverOf T G U n s) :
    IsDynamicalCoverOf T F U n s := Subset.trans F_G h

theorem dynnet_monotone_space {T : X → X} {F G : Set X} (F_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynamicalNetOf T F U n s) :
    IsDynamicalNetOf T G U n s := ⟨Subset.trans h.1 F_G, h.2⟩

theorem mincard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Mincard T F U n) := by
  intro F G F_G
  simp only [mincard_eq_sInf T F U n, mincard_eq_sInf T G U n]
  exact sInf_le_sInf (image_mono (image_mono fun _ ↦ dyncover_monotone_space F_G))

theorem maxcard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Maxcard T F U n) := by
  intro F G F_G
  simp only [maxcard_eq_sSup T F U n, maxcard_eq_sSup T G U n]
  exact sSup_le_sSup (image_mono (image_mono (fun _ ↦ dynnet_monotone_space F_G)))

theorem CoverEntropyInfUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropyInfUni T F U) := by
  intro F G F_G
  refine liminf_le_liminf <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact mincard_monotone_space T U n F_G

theorem CoverEntropySupUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropySupUni T F U) := by
  intro F G F_G
  refine limsup_le_limsup <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact mincard_monotone_space T U n F_G

theorem NetEntropyInfUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropyInfUni T F U) := by
  intro F G F_G
  refine liminf_le_liminf <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact maxcard_monotone_space T U n F_G

theorem NetEntropySupUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropySupUni T F U) := by
  intro F G F_G
  refine limsup_le_limsup <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact maxcard_monotone_space T U n F_G

theorem CoverEntropyInf_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ CoverEntropyInf T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ CoverEntropyInfUni_monotone_space T U F_G)

theorem CoverEntropySup_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ CoverEntropySup T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ CoverEntropySupUni_monotone_space T U F_G)

theorem NetEntropyInf_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ NetEntropyInf T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ NetEntropyInfUni_monotone_space T U F_G)

theorem NetEntropySup_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ NetEntropySup T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ NetEntropySupUni_monotone_space T U F_G)

/-! ### Topological entropy of closure -/

open DynamicalUniformity Function Uniformity UniformSpace

theorem dyncover_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T) {F : Set X}
    {U V : Set (X × X)} (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X}
    (s_cover : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T (closure F) (U ○ V) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  rw [id_eq] at W_V
  refine dyncover_antitone_uni (compRel_mono (Subset.refl U) W_V) (fun x x_clos ↦ ?_)
  rcases mem_closure_iff_ball.1 x_clos (dynamical_uni_of_uni h W_uni n) with ⟨y, y_x, y_F⟩
  specialize s_cover y_F
  simp only [iUnion_coe_set, mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨z, z_s, y_z⟩
  simp only [iUnion_coe_set, mem_iUnion, exists_prop]
  use z, z_s
  rw [mem_ball_symmetry (dynamical_uni_of_symm T W_symm n)] at y_x
  exact ball_mono (dynamical_uni_of_comp T U W n) z (mem_ball_comp y_z y_x)

theorem mincard_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T) (F : Set X)
    (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    Mincard T (closure F) (U ○ V) n ≤ Mincard T F U n := by
  rcases eq_top_or_lt_top (Mincard T F U n) with (h' | h')
  . exact h' ▸ le_top
  . rcases (finite_mincard_iff T F U n).1 h' with ⟨s, s_cover, s_mincard⟩
    exact s_mincard ▸ mincard_le_card (dyncover_of_closure h V_uni s_cover)

theorem CoverEntropyInfUni_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
  (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    CoverEntropyInfUni T (closure F) (U ○ V) ≤ CoverEntropyInfUni T F U := by
  refine liminf_le_liminf <| Filter.eventually_of_forall (fun n ↦ ?_)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact mincard_of_closure h F U V_uni n

theorem CoverEntropySupUni_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    CoverEntropySupUni T (closure F) (U ○ V) ≤ CoverEntropySupUni T F U := by
  refine limsup_le_limsup <| Filter.eventually_of_forall (fun n ↦ ?_)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact mincard_of_closure h F U V_uni n

theorem CoverEntropyInf_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) :
    CoverEntropyInf T (closure F) = CoverEntropyInf T F := by
  refine le_antisymm (iSup₂_le fun U U_uni ↦ ?_)
    (CoverEntropyInf_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (CoverEntropyInfUni_antitone_uni T (closure F) V_U)
    (CoverEntropyInfUni_of_closure h F V V_uni))

theorem CoverEntropySup_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) :
    CoverEntropySup T (closure F) = CoverEntropySup T F := by
  refine le_antisymm (iSup₂_le fun U U_uni ↦ ?_)
    (CoverEntropySup_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (CoverEntropySupUni_antitone_uni T (closure F) V_U)
    (CoverEntropySupUni_of_closure h F V V_uni))

/-! ### Topological entropy of unions -/

theorem dyncover_of_union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynamicalCoverOf T F U n s) (ht : IsDynamicalCoverOf T G U n t) :
    IsDynamicalCoverOf T (F ∪ G) U n (s ∪ t) := by
  intro x x_FG
  rcases x_FG with (x_F | x_G)
  . refine mem_of_subset_of_mem (iSup₂_mono' fun y y_s ↦ ?_) (hs x_F)
    use y, (mem_union_left t y_s)
  . refine mem_of_subset_of_mem (iSup₂_mono' fun y y_t ↦ ?_) (ht x_G)
    use y, (mem_union_right s y_t)

theorem mincard_union_le (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T (F ∪ G) U n ≤ Mincard T F U n + Mincard T G U n := by
  classical
  rcases eq_top_or_lt_top (Mincard T F U n) with (hF | hF)
  . rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (Mincard T G U n) with (hG | hG)
  . rw [hG, add_top]; exact le_top
  rcases (finite_mincard_iff T F U n).1 hF with ⟨s, s_cover, s_mincard⟩
  rcases (finite_mincard_iff T G U n).1 hG with ⟨t, t_cover, t_mincard⟩
  rw [← s_mincard, ← t_mincard]
  have := dyncover_of_union s_cover t_cover
  rw [← Finset.coe_union s t] at this
  apply le_trans (mincard_le_card this) (le_trans (WithTop.coe_mono (Finset.card_union_le s t)) _)
  norm_cast

theorem CoverEntropySupUni_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    CoverEntropySupUni T (F ∪ G) U = max (CoverEntropySupUni T F U) (CoverEntropySupUni T G U) := by
  classical
  rcases F.eq_empty_or_nonempty with (rfl | hF)
  · simp only [empty_union, CoverEntropySupUni_of_empty, bot_le, max_eq_right]
  apply le_antisymm _ (max_le (CoverEntropySupUni_monotone_space T U subset_union_left)
    (CoverEntropySupUni_monotone_space T U subset_union_right))
  simp only
  have key : ∀ n : ℕ, log (Mincard T (F ∪ G) U n) / n
      ≤ log (max (Mincard T F U n) (Mincard T G U n)) / n + log (2 : ENNReal) / n := by
    intro n
    have h_logm : 0 ≤ log (max (Mincard T F U n) (Mincard T G U n)) := by
      rw [Monotone.map_max log_monotone]
      exact le_trans (log_mincard_nonneg_of_nonempty T hF U n) (le_max_left _ _)
    rw [← div_right_distrib_of_nonneg (c := n) h_logm (zero_le_log_iff.2 one_le_two)]
    apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    rw [← log_mul_add]
    apply log_monotone
    norm_cast
    rw [mul_two]
    exact le_trans (mincard_union_le T F G U n) (add_le_add (le_max_left _ _) (le_max_right _ _))
  apply le_trans (limsup_le_limsup (Filter.eventually_of_forall fun n ↦ key n))
  have := Filter.Tendsto.limsup_eq <| EReal.tendsto_const_div_atTop_nhds_zero_nat
    (ne_of_gt (bot_lt_log_iff.2 Nat.ofNat_pos)) (ne_of_lt (log_lt_top_iff.2 two_lt_top))
  apply le_trans (limsup_add_le_add_limsup (Or.inr (this ▸ EReal.zero_ne_top))
    (Or.inr (this ▸ EReal.zero_ne_bot)))
  apply le_of_eq
  unfold CoverEntropySupUni
  rw [this, add_zero, ← limsup_max]
  congr
  ext n
  rw [Monotone.map_max log_monotone,
    Monotone.map_max (EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n))]

theorem CoverEntropySup_union [UniformSpace X] (T : X → X) (F G : Set X) :
    CoverEntropySup T (F ∪ G) = max (CoverEntropySup T F) (CoverEntropySup T G) := by
  unfold CoverEntropySup
  rw [iSup_subtype', iSup_subtype', iSup_subtype', ← _root_.sup_eq_max, ← iSup_sup_eq]
  congr
  ext U_uni
  exact CoverEntropySupUni_union T F G U_uni.1

theorem CoverEntropyInf_union_of_inv [UniformSpace X] (T : X → X) {F G : Set X}
    (hF : MapsTo T F F) (hG : MapsTo T G G) :
    CoverEntropyInf T (F ∪ G) = max (CoverEntropyInf T F) (CoverEntropyInf T G) := by
  rw [CoverEntropyInf_eq_CoverEntropySup_of_inv T hF,
    CoverEntropyInf_eq_CoverEntropySup_of_inv T hG, ← CoverEntropySup_union T F G]
  exact CoverEntropyInf_eq_CoverEntropySup_of_inv T (MapsTo.union_union hF hG)

/-! ### Topological entropy of finite unions -/

/-theorem dyncover_of_iUnion {ι : Type*} {T : X → X} {F : ι → Set X} {U : Set (X × X)} {n : ℕ}
    {s : ι → Set X} (h : ∀ i, IsDynamicalCoverOf T (F i) U n (s i)) :
    IsDynamicalCoverOf T (⋃ i, F i) U n (⋃ i, s i) := by
  intro x x_F
  rcases (mem_iUnion.1 x_F) with ⟨i, x_Fi⟩
  rcases (mem_iUnion₂.1 (h i x_Fi)) with ⟨y, y_si, x_y⟩
  apply mem_iUnion₂.2
  use y, mem_iUnion_of_mem i y_si-/

theorem dyncover_of_biUnion {ι : Type*} (s: Set ι) {T : X → X} {F : ι → Set X} {U : Set (X × X)}
    {n : ℕ} {t : ι → Set X} (h : ∀ i ∈ s, IsDynamicalCoverOf T (F i) U n (t i)) :
    IsDynamicalCoverOf T (⋃ i ∈ s, F i) U n (⋃ i ∈ s, t i) := by
  intro x x_F
  rcases (mem_iUnion₂.1 x_F) with ⟨i, i_s, x_Fi⟩
  rcases (mem_iUnion₂.1 (h i i_s x_Fi)) with ⟨y, y_si, x_y⟩
  apply mem_iUnion₂.2
  use y, mem_biUnion i_s y_si

/-theorem mincard_iUnion_le {ι : Type*} [Fintype ι] (T : X → X) (F : ι → Set X) (U : Set (X × X))
    (n : ℕ) :
    Mincard T (⋃ i, F i) U n ≤ ∑ i, Mincard T (F i) U n := by
  classical
  rcases isEmpty_or_nonempty ι
  · simp
  by_cases h : ∃ i, (Mincard T (F i) U n) = ⊤
  · apply le_of_le_of_eq le_top (Eq.symm _)
    apply WithTop.sum_eq_top_iff.2
    simp only [Finset.mem_univ, true_and]
    exact h
  push_neg at h
  choose ! s hs using (fun i ↦ (finite_mincard_iff T (F i) U n).1 (Ne.lt_top (h i)))
  rw [forall_and] at hs
  rcases hs with ⟨si_cover, si_card⟩
  rw [← Fintype.sum_congr _ _ si_card]
  norm_cast
  apply le_trans (mincard_le_card _) (WithTop.coe_le_coe.2 Finset.card_biUnion_le)
  simp only [Finset.coe_biUnion, Finset.coe_univ, mem_univ, iUnion_true]
  exact dyncover_of_iUnion si_cover-/

theorem mincard_biUnion_le {ι : Type*} (s : Finset ι) (T : X → X) (F : ι → Set X) (U : Set (X × X))
    (n : ℕ) :
    Mincard T (⋃ i ∈ s, F i) U n ≤ ∑ i ∈ s, Mincard T (F i) U n := by
  classical
  by_cases h : ∃ i ∈ s, (Mincard T (F i) U n) = ⊤
  · exact le_of_le_of_eq le_top (Eq.symm (WithTop.sum_eq_top_iff.2 h))
  push_neg at h
  choose ! t ht using (fun i i_s ↦ (finite_mincard_iff T (F i) U n).1 (Ne.lt_top (h i i_s)))
  rw [forall₂_and] at ht
  rcases ht with ⟨ti_cover, ti_card⟩
  rw [← Finset.sum_congr (Eq.refl s) ti_card]
  norm_cast
  apply le_trans (mincard_le_card _) (WithTop.coe_le_coe.2 Finset.card_biUnion_le)
  simp only [Finset.coe_biUnion, Finset.mem_coe]
  exact dyncover_of_biUnion s (t := fun i ↦ Finset.toSet (t i)) ti_cover

theorem CoverEntropySupUni_biUnion {ι : Type*} (s : Finset ι) (T : X → X) (F : ι → Set X)
    (U : Set (X × X)) :
    CoverEntropySupUni T (⋃ i ∈ s, F i) U = ⨆ i ∈ s, CoverEntropySupUni T (F i) U := by
  classical
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  by_cases h : ∀ i ∈ s, F i = ∅
  · apply Eq.symm
    rw [iUnion₂_congr h]
    simp only [iUnion_empty, CoverEntropySupUni_of_empty, iSup_eq_bot]
    exact fun i i_s ↦ h i i_s ▸ CoverEntropySupUni_of_empty
  push_neg at h
  rcases h with ⟨i0, i0_s, hi0⟩
  apply le_antisymm; swap
  · apply le_of_le_of_eq (Monotone.le_map_iSup₂ (CoverEntropySupUni_monotone_space T U) _)
    simp only [iSup_eq_iUnion]
  have key : ∀ n : ℕ, log (Mincard T (⋃ i ∈ s, F i) U n) / n
      ≤ log (⨆ i ∈ s, Mincard T (F i) U n) / n + log (s.card : ENNReal) / n := by
    intro n
    have h_logs : 0 ≤ log (⨆ i ∈ s, Mincard T (F i) U n) := by
      apply le_trans _ (Monotone.le_map_iSup₂ log_monotone _)
      exact le_trans (log_mincard_nonneg_of_nonempty T hi0 U n)
        (le_iSup₂ (f := fun i i_s ↦ log (Mincard T (F i) U n)) i0 i0_s)
    have h_scar : 0 ≤ log s.card := by
      apply zero_le_log_iff.2
      rw [Nat.one_le_cast]
      exact Finset.one_le_card.2 hs
    rw [← div_right_distrib_of_nonneg (c := n) h_logs h_scar]
    apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    rw [← log_mul_add]
    apply log_monotone
    sorry
  apply le_trans (limsup_le_limsup (Filter.eventually_of_forall fun n ↦ key n))
  have : Filter.atTop.limsup (fun n : ℕ ↦ log (s.card : ENNReal) / n) = 0 :=
    Filter.Tendsto.limsup_eq <| EReal.tendsto_const_div_atTop_nhds_zero_nat
      (ne_of_gt (bot_lt_log_iff.2 (Nat.cast_pos.2 (Finset.Nonempty.card_pos hs))))
      (ne_of_lt (log_lt_top_iff.2 (Ne.lt_top (WithTop.natCast_ne_top s.card))))
  apply le_trans (limsup_add_le_add_limsup (Or.inr (this ▸ EReal.zero_ne_top))
    (Or.inr (this ▸ EReal.zero_ne_bot)))
  apply le_of_eq
  unfold CoverEntropySupUni
  rw [this, add_zero]
  sorry

  /--/






theorem CoverEntropySupUni_iUnion {ι : Type*} [Fintype ι] (T : X → X) (F : ι → Set X)
    (U : Set (X × X)) :
    CoverEntropySupUni T (⋃ i, F i) U = ⨆ i, CoverEntropySupUni T (F i) U := by
  rcases isEmpty_or_nonempty ι
  · simp
  by_cases h : ∀ i, F i = ∅
  · simp [h]
  push_neg at h
  rcases h with ⟨i0, hi0⟩
  apply le_antisymm; swap
  · apply le_trans (Monotone.le_map_iSup (CoverEntropySupUni_monotone_space T U))
    rw [iSup_eq_iUnion]
  classical
  have key : ∀ n : ℕ, log (Mincard T (⋃ i, F i) U n) / n
      ≤ log (⨆ i, Mincard T (F i) U n) / n + log (Fintype.card ι : ENNReal) / n := by
    intro n
    have h_logs : 0 ≤ log (⨆ i, Mincard T (F i) U n) := by
      apply le_trans _ (Monotone.le_map_iSup log_monotone)
      exact le_trans (log_mincard_nonneg_of_nonempty T hi0 U n)
        (le_iSup (fun i ↦ log (Mincard T (F i) U n)) i0)
    sorry
    /-rw [← div_right_distrib_of_nonneg (c := n) h_logm (zero_le_log_iff.2 one_le_two)]
    apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    rw [← log_mul_add]
    apply log_monotone
    norm_cast
    rw [mul_two]
    exact le_trans (mincard_union_l-/
  apply le_trans (limsup_le_limsup (Filter.eventually_of_forall fun n ↦ key n))
  have : Filter.atTop.limsup (fun n : ℕ ↦ log (Fintype.card ι : ENNReal) / n) = 0 :=
    Filter.Tendsto.limsup_eq <| EReal.tendsto_const_div_atTop_nhds_zero_nat
      (ne_of_gt (bot_lt_log_iff.2 (Nat.cast_pos.2 Fintype.card_pos)))
      (ne_of_lt (log_lt_top_iff.2 (Ne.lt_top (WithTop.natCast_ne_top (Fintype.card ι)))))
  apply le_trans (limsup_add_le_add_limsup (Or.inr (this ▸ EReal.zero_ne_top))
    (Or.inr (this ▸ EReal.zero_ne_bot)))
  apply le_of_eq
  unfold CoverEntropySupUni
  rw [this, add_zero]
  have next_goal := limsup_finset_sup (α := EReal)
  sorry




end Entropy

#lint
