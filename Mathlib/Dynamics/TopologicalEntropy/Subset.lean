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

theorem CoverEntropySup_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, CoverEntropySup T (F i) ≤ CoverEntropySup T (⋃ i, F i) :=
  iSup_le (fun i ↦ (CoverEntropySup_monotone_space T (subset_iUnion F i)))

theorem CoverEntropySup_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, CoverEntropySup T (F i) ≤ CoverEntropySup T (⋃ i ∈ s, F i) :=
  iSup₂_le (fun _ i_s ↦ (CoverEntropySup_monotone_space T (subset_biUnion_of_mem i_s)))

theorem CoverEntropyInf_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, CoverEntropyInf T (F i) ≤ CoverEntropyInf T (⋃ i, F i) :=
  iSup_le (fun i ↦ (CoverEntropyInf_monotone_space T (subset_iUnion F i)))

theorem CoverEntropyInf_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, CoverEntropyInf T (F i) ≤ CoverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le (fun _ i_s ↦ (CoverEntropyInf_monotone_space T (subset_biUnion_of_mem i_s)))

theorem CoverEntropySup_finite_iUnion {ι : Type*} [UniformSpace X] [Fintype ι] (T : X → X)
    (F : ι → Set X) :
    CoverEntropySup T (⋃ i, F i) = ⨆ i, CoverEntropySup T (F i) := by
  apply Fintype.induction_empty_option (P := fun ι _ ↦ ∀ F : ι → Set X,
    CoverEntropySup T (⋃ i, F i) = ⨆ i, CoverEntropySup T (F i))
  · intro α β _ α_β h F
    specialize h (F ∘ α_β)
    simp only [comp_apply] at h
    rw [← iUnion_congr_of_surjective (g := F) α_β (Equiv.surjective α_β) (fun _ ↦ comp_apply), h]
    exact Equiv.iSup_comp (g := fun i : β ↦ CoverEntropySup T (F i)) α_β
  · intro _
    simp only [iUnion_of_empty, CoverEntropySup_of_empty, ciSup_of_empty]
  · intro α _ h F
    rw [iSup_option, iUnion_option, CoverEntropySup_union T (F none) (⋃ i, F (some i)),
      _root_.sup_eq_max]
    congr
    exact h (fun i : α ↦ F (some i))

theorem CoverEntropySup_finite_biUnion {ι : Type*} [UniformSpace X] (s : Finset ι) (T : X → X)
    (F : ι → Set X) :
    CoverEntropySup T (⋃ i ∈ s, F i) = ⨆ i ∈ s, CoverEntropySup T (F i) := by
  have fin_coe : Fintype { i // i ∈ s } := FinsetCoe.fintype s
  have := @CoverEntropySup_finite_iUnion X {i // i ∈ s} _ fin_coe T (fun i ↦ F i)
  rw [iSup_subtype', ← this, iUnion_subtype]

theorem CoverEntropyInf_finite_iUnion_of_inv {ι : Type*} [UniformSpace X] [Fintype ι] {T : X → X}
    {F : ι → Set X} (h : ∀ i, MapsTo T (F i) (F i)) :
    CoverEntropyInf T (⋃ i, F i) = ⨆ i, CoverEntropyInf T (F i) := by
  rw [CoverEntropyInf_eq_CoverEntropySup_of_inv T (mapsTo_iUnion_iUnion h),
    CoverEntropySup_finite_iUnion T F]
  exact iSup_congr (fun i ↦ Eq.symm (CoverEntropyInf_eq_CoverEntropySup_of_inv T (h i)))

theorem CoverEntropyInf_finite_biUnion_of_inv {ι : Type*} [UniformSpace X] (s : Finset ι)
    (T : X → X) {F : ι → Set X} (h : ∀ i ∈ s, MapsTo T (F i) (F i)) :
    CoverEntropyInf T (⋃ i ∈ s, F i) = ⨆ i ∈ s, CoverEntropyInf T (F i) := by
  rw [CoverEntropyInf_eq_CoverEntropySup_of_inv T (mapsTo_iUnion₂_iUnion₂ h),
    CoverEntropySup_finite_biUnion s T F]
  exact biSup_congr' (fun i i_s ↦ Eq.symm (CoverEntropyInf_eq_CoverEntropySup_of_inv T (h i i_s)))

end Entropy

#lint
