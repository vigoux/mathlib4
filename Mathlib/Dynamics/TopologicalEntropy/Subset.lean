/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import BET.TopologicalEntropy.DynamicalNet

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

namespace EntropyMonotoneSpace

open ERealDiv ENNReal DynamicalCover

variable {X : Type _}

theorem cover_of_monotone_space {T : X → X} {F G : Set X} (F_sub_G : F ⊆ G) {U : Set (X × X)}
    {n : ℕ} {s : Set X} (h : IsDynamicalCoverOf T G U n s) :
    IsDynamicalCoverOf T F U n s :=
  Set.Subset.trans F_sub_G h

theorem cover_mincard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Mincard T F U n) := by
  intro F G F_sub_G
  simp only [mincard_eq_sInf T F U n, mincard_eq_sInf T G U n]
  exact sInf_le_sInf (Set.image_mono (Set.image_mono fun _ ↦ cover_of_monotone_space F_sub_G))

theorem cover_entropy_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropy T F U) := by
  intro F G F_sub_G
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_monotone_space T U n F_sub_G

theorem cover_entropy'_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropy' T F U) := by
  intro F G F_sub_G
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_monotone_space T U n F_sub_G

theorem entropy_monotone_space₁ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy T F) := by
  intro F G F_sub_G
  apply iSup₂_mono; intros U _
  exact cover_entropy_monotone_space T U F_sub_G

theorem entropy'_monotone_space₁ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy' T F) := by
  intro F G F_sub_G
  apply iSup₂_mono; intros U _
  exact cover_entropy'_monotone_space T U F_sub_G

end EntropyMonotoneSpace

namespace EntropyMonotoneSpace

open ERealDiv ENNReal DynamicalNet

variable {X : Type _}

theorem net_of_monotone_space {T : X → X} {F G : Set X} (F_sub_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynamicalNetOf T F U n s) :
    IsDynamicalNetOf T G U n s := ⟨Set.Subset.trans h.1 F_sub_G, h.2⟩

theorem net_maxcard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Maxcard T F U n) := by
  intro F G F_sub_G
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T G U n]
  apply sSup_le_sSup (Set.image_mono (Set.image_mono _))
  exact fun _ ↦ net_of_monotone_space F_sub_G

theorem net_entropy_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropy T F U) := by
  intros F G F_sub_G
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _ (log_monotone _)
  rw [ENat.toENNReal_le]
  exact net_maxcard_monotone_space T U n F_sub_G

theorem net_entropy'_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropy' T F U) := by
  intros F G F_sub_G
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _ (log_monotone _)
  rw [ENat.toENNReal_le]
  exact net_maxcard_monotone_space T U n F_sub_G

theorem entropy_monotone_space₂ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy T F) :=
  fun _ _ F_sub_G ↦ iSup₂_mono fun U _ ↦ net_entropy_monotone_space T U F_sub_G

theorem entropy'_monotone_space₂ [UniformSpace X] (T : X → X)  :
    Monotone (fun F : Set X ↦ Entropy' T F) :=
  fun _ _ F_sub_G ↦ iSup₂_mono fun U _ ↦ net_entropy'_monotone_space T U F_sub_G

end EntropyMonotoneSpace


namespace EntropyClosure

open Function UniformSpace ERealDiv ENNReal DynamicalCover DynamicalUniformity

variable {X : Type _} [UniformSpace X] {T : X → X} (h : UniformContinuous T)

theorem dyncover_of_closure {F : Set X} {U V : Set (X × X)} (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X}
    (s_cover : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T (closure F) (compRel U V) n s := by
  /-WLOG, the uniformity V can be assumed symmetric.-/
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_sub_V⟩
  rw [id_eq] at W_sub_V
  apply dyncover_antitone_uni (compRel_mono (Set.Subset.refl U) W_sub_V); clear W_sub_V V_uni V
  /-Main argument.-/
  intro x x_in_clos
  rcases mem_closure_iff_ball.1 x_in_clos (dynamical_of_uni_is_uni h W_uni n)
    with ⟨y, y_in_ball_x, y_in_F⟩
  specialize s_cover y_in_F
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨z, z_in_s, y_in_ball_z⟩
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop]
  use z
  apply And.intro z_in_s
  rw [mem_ball_symmetry (dynamical_of_symm_is_symm T W_symm n)] at y_in_ball_x
  exact ball_mono (dynamical_of_comp_is_comp T U W n) z (mem_ball_comp y_in_ball_z y_in_ball_x)

theorem cover_mincard_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X)
    (n : ℕ) :
    Mincard T (closure F) (compRel U V) n ≤ Mincard T F U n := by
  rcases eq_top_or_lt_top (Mincard T F U n) with (mincard_infi | mincard_fin)
  . exact mincard_infi ▸ le_top
  . rcases (finite_mincard_iff T F U n).1 mincard_fin with ⟨s, s_cover, s_mincard⟩
    exact s_mincard ▸ mincard_le_card (dyncover_of_closure h V_uni s_cover)

theorem cover_entropy_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    CoverEntropy T (closure F) (compRel U V) ≤ CoverEntropy T F U := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _ (log_monotone _)
  rw [ENat.toENNReal_le]
  exact cover_mincard_of_closure h F U V_uni n

theorem cover_entropy'_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)}
    (V_uni : V ∈ 𝓤 X) :
    CoverEntropy' T (closure F) (compRel U V) ≤ CoverEntropy' T F U := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _ (log_monotone _)
  rw [ENat.toENNReal_le]
  exact cover_mincard_of_closure h F U V_uni n

theorem entropy_of_closure (F : Set X) :
    Entropy T (closure F) = Entropy T F := by
  apply le_antisymm (iSup₂_le _) (EntropyMonotoneSpace.entropy_monotone_space₁ T (@subset_closure X F _))
  intro U U_uni
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_comp_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (cover_entropy_antitone_uni T (closure F) V_comp_U)
    (cover_entropy_of_closure h F V V_uni))

theorem entropy'_of_closure (F : Set X) :
    Entropy' T (closure F) = Entropy' T F := by
  apply le_antisymm (iSup₂_le _) (EntropyMonotoneSpace.entropy'_monotone_space₁ T (@subset_closure X F _))
  intro U U_uni
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_comp_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (cover_entropy'_antitone_uni T (closure F) V_comp_U)
    (cover_entropy'_of_closure h F V V_uni))

end EntropyClosure



/-!
# Topological entropy of unions
The topological entropy of an union is the maximum of the topological entropies.

TODO: Finish the proof. The manipulation of logarithms and limits is still too painful.

TODO: extend it to finite unions.
-/

namespace EntropyUnion

open ERealDiv ENNReal Misc DynamicalCover EntropyMonotoneSpace

variable {X : Type _}

theorem cover_of_union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynamicalCoverOf T F U n s) (ht : IsDynamicalCoverOf T G U n t) :
    IsDynamicalCoverOf T (F ∪ G) U n (s ∪ t) := by
  intro x x_in_FG
  rcases x_in_FG with (x_in_F | x_in_G)
  . specialize hs x_in_F
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hs
    rcases hs with ⟨y, ⟨y_in_s, hy⟩⟩
    simp only [Set.iUnion_coe_set, Set.mem_union, Set.mem_iUnion, exists_prop]
    use y
    exact ⟨Or.inl y_in_s, hy⟩
  . specialize ht x_in_G
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at ht
    rcases ht with ⟨y, ⟨y_in_t, hy⟩⟩
    simp only [Set.iUnion_coe_set, Set.mem_union, Set.mem_iUnion, exists_prop]
    use y
    exact ⟨Or.inr y_in_t, hy⟩

theorem cover_mincard_union (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T (F ∪ G) U n ≤ Mincard T F U n + Mincard T G U n := by
  classical
  /-WLOG, `F` admits a finite cover.-/
  rcases eq_top_or_lt_top (Mincard T F U n) with F_infi | F_fin
  . rw [F_infi, top_add]; exact le_top
  /-WLOG, `G` admits a finite cover.-/
  rcases eq_top_or_lt_top (Mincard T G U n) with G_infi | G_fin
  . rw [G_infi, add_top]; exact le_top
  /-Get some minimal covers of `F` and `G`.-/
  rw [finite_mincard_iff T F U n] at F_fin
  rcases F_fin with ⟨s, ⟨s_cover, s_mincard⟩⟩
  rw [← s_mincard]; clear s_mincard
  rw [finite_mincard_iff T G U n] at G_fin
  rcases G_fin with ⟨t, ⟨t_cover, t_mincard⟩⟩
  rw [← t_mincard]; clear t_mincard
  /-Construct a cover of `F ×ˢ G` and show that is has the right cardinality-/
  have := cover_of_union s_cover t_cover
  rw [← Finset.coe_union s t] at this
  apply le_trans (mincard_le_card this) (le_trans (WithTop.coe_mono (Finset.card_union_le s t)) _)
  simp
/-
theorem cover_entropy'_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    CoverEntropy' T (F ∪ G) U = max (CoverEntropy' T F U) (CoverEntropy' T G U) := by
  classical
  /-WLOG, `F` admits a finite cover.-/
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · simp only [Set.empty_union, cover_entropy'_of_empty, bot_le, max_eq_right]
  /-WLOG, `G` admits a finite cover.-/
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  · simp only [Set.union_empty, cover_entropy'_of_empty, bot_le, max_eq_left]
  /-One inequality follows trivially from the monotonicity of the entropy.-/
  apply le_antisymm _ (max_le (cover_entropy'_monotone_space T U (Set.subset_union_left F G))
    (cover_entropy'_monotone_space T U (Set.subset_union_right F G)))
  simp only
  /-Main case.-/
  have nneg_log_max := fun n : ℕ => log_monotone (ENat.toENNReal_le.2 (le_trans
    ((pos_mincard_of_nonempty T F U n).1 F_nemp) (le_max_left (Mincard T F U n) (Mincard T G U n)) ) )
  simp at nneg_log_max
  have key : ∀ n : ℕ, ENNReal.log (Mincard T (F ∪ G) U n) / (n : ENNReal)
    ≤ ENNReal.log (2) / (n : ENNReal)
    + ENNReal.log (max (Mincard T F U n) (Mincard T G U n)) / (n : ENNReal) := by
    intro n
    rw [← @EReal.div_right_distrib_of_nneg _ _ n (log_one_le_iff.1 one_le_two) (nneg_log_max n)]
    apply EReal.div_left_mono n
    rw [← log_mul_add]
    apply log_monotone
    apply le_trans (ENat.toENNReal_le.2 (cover_mincard_union T F G U n))
    rw [two_mul, ENat.toENNReal_add]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  apply le_trans (Filter.limsup_le_limsup (@Filter.eventually_of_forall ℕ _ Filter.atTop key))
  clear key
  apply le_trans (EReal.limsup_add_le_add_limsup _ _)
  . have limsup_zero : Filter.limsup (fun n : ℕ => log 2 / (n : ENNReal)) Filter.atTop = 0 := by
      apply Filter.Tendsto.limsup_eq
      have : (fun n : ℕ => log (2) / (n : ENNReal))
        = (fun p : EReal × EReal => p.1 * p.2)
        ∘ (fun n : ℕ => Prod.mk (ENNReal.log (2)) ((n⁻¹ : ENNReal) : EReal)) := by
        ext n
        simp
        sorry
      have log_ne_zero : ENNReal.log (2) ≠ 0 := by sorry
      have log_ne_bot : ENNReal.log (2) ≠ ⊥ := by sorry
      have log_ne_top : ENNReal.log (2) ≠ ⊤ := by sorry
      have key := @ERealMulCont.continuousAt_mul (log (2), 0)
        (Or.inl log_ne_zero) (Or.inl log_ne_zero) (Or.inl log_ne_bot) (Or.inl log_ne_top)
      replace key := ContinuousAt.tendsto key
      simp at key
      sorry
    unfold CoverEntropy'
    rw [limsup_zero, zero_add, ← EReal.limsup_max]; clear limsup_zero
    apply Filter.limsup_le_limsup
    . apply Filter.eventually_of_forall
      intro n
      simp only []
      rw [← Monotone.map_max (EReal.div_left_mono n)]
      apply EReal.div_left_mono n
      rw [Monotone.map_max log_monotone]
    . use ⊥; simp
    . use ⊤; simp
  . apply Or.inl (ne_of_gt _)
    apply lt_of_lt_of_le EReal.bot_lt_zero
    apply EReal.const_le_limsup_forall
    intro n
    apply EReal.nneg_div
    apply log_one_le_iff.1
    simp only [Nat.one_le_ofNat]
  . apply Or.inr
    apply ne_of_gt
    apply lt_of_lt_of_le EReal.bot_lt_zero
    rw [← @Filter.limsup_const EReal ℕ _ Filter.atTop _ 0]
    apply EReal.const_le_limsup_forall
    intro n
    simp only [Filter.limsup_const]
    apply EReal.nneg_div
    specialize nneg_log_max n
    exact nneg_log_max

theorem entropy'_union [UniformSpace X] (T : X → X) (F G : Set X) :
    Entropy' T (F ∪ G) = max (Entropy' T F) (Entropy' T G) := by
  sorry
-/

end EntropyUnion

#lint
