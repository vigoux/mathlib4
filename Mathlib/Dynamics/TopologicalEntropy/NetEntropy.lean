/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single lemma (theorem `subset_restriction_entropy` in `.Morphism`) will give the equivalence between
both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal`.

We relate in this file `CoverEntropy` and `NetEntropy`. This file is downstream of
`Mathlib.Dynamics.TopologicalEntropy.CoverEntropy` since the submultiplicative argument there is
more natural for covers.

## Main definitions
- `IsDynamicalNetOf`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `Maxcard`: maximal cardinal of a dynamical net. Takes values in `ℕ∞`.
- `NetEntropyInfUni`/`NetEntropySupUni`: exponential growth of `Maxcard`. The former is
defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `NetEntropyInf`/`NetEntropySup`: supremum of `NetEntropyInfUni`/`NetEntropySupUni` over
all uniformities (or limit as the uniformity goes to the diagonal). These are Bowen-Dinaburg's
versions of the topological entropy with nets. Take values in `EReal`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace DynamicalNet

open DynamicalUniformity Set Uniformity UniformSpace

variable {X : Type*}

/-! ### Dynamical nets -/

/-- Given a subset `F`, a uniform neighborhood `U` and an integer `n`, a subset `s` of `F` is a
`(U, n)`-dynamical net of `F` if no two orbits of length `n` of points in `s` shadow each other.-/
def IsDynamicalNetOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
    s ⊆ F ∧ s.PairwiseDisjoint (fun x : X ↦ ball x (DynamicalUni T U n))

theorem dynnet_monotone_time {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n)
    {s : Set X} (h : IsDynamicalNetOf T F U m s) :
    IsDynamicalNetOf T F U n s := by
  use h.1
  refine PairwiseDisjoint.mono h.2 (fun x ↦ ?_)
  apply ball_mono (dynamical_uni_antitone_time T U m_n)

theorem dynnet_antitone_uni {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V) {n : ℕ}
    {s : Set X} (h : IsDynamicalNetOf T F V n s) :
    IsDynamicalNetOf T F U n s := by
  use h.1
  refine PairwiseDisjoint.mono h.2 (fun x ↦ ?_)
  apply ball_mono (dynamical_uni_monotone_uni T n U_V)

theorem dynnet_by_empty (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    IsDynamicalNetOf T F U n ∅ :=
  ⟨empty_subset F, pairwise_empty _⟩

theorem dynnet_by_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynamicalNetOf T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

open DynamicalCover

theorem dynnet_card_le_dyncover_card {T : X → X} {F : Set X} {U : Set (X × X)}
    (U_symm : SymmetricRel U) {n : ℕ} {s t : Finset X} (hs : IsDynamicalNetOf T F U n s)
    (ht : IsDynamicalCoverOf T F U n t) :
    s.card ≤ t.card := by
  have : ∀ x ∈ s, ∃ z ∈ t, x ∈ ball z (DynamicalUni T U n) := by
    intro x x_s
    specialize ht (hs.1 x_s)
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at ht
    exact ht
  choose! F s_to_t using this
  simp only [mem_ball_symmetry (dynamical_uni_of_symm_is_symm T U_symm n)] at s_to_t
  apply Finset.card_le_card_of_injOn F (fun x x_s ↦ (s_to_t x x_s).1)
  intro x x_s y y_s Fx_Fy
  exact PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_to_t x x_s).2 (Fx_Fy ▸ (s_to_t y y_s).2)

/-! ### Maximal cardinal of dynamical nets -/

/--The largest cardinal of a `(U, n)`-dynamical net of F. Takes values in `ℕ∞`, and is infinite
if and only if `F` admits nets of arbitrarily large size.-/
noncomputable def Maxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynamicalNetOf T F U n s), (s.card : ℕ∞)

theorem maxcard_eq_sSup (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n
    = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s})) := by
  unfold Maxcard
  rw [← image_comp, sSup_image]
  simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]

theorem card_le_maxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalNetOf T F U n s) :
    s.card ≤ Maxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h

theorem maxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ Maxcard T F U n) := by
  intros m n m_n
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T F U m]
  apply sSup_le_sSup
  apply image_subset
  apply image_subset
  exact fun s ↦ dynnet_monotone_time m_n

theorem maxcard_antitone_uni (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ Maxcard T F U n) := by
  intros U V U_V
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T F V n]
  apply sSup_le_sSup
  apply image_subset
  apply image_subset
  exact fun s ↦ dynnet_antitone_uni U_V

theorem finite_maxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynamicalNetOf T F U n s ∧ (s.card : ℕ∞) = Maxcard T F U n := by
  apply Iff.intro <;> intro h
  · rcases WithTop.ne_top_iff_exists.1 (ne_of_lt h) with ⟨k, k_maxcard⟩
    rw [← k_maxcard]
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    rw [maxcard_eq_sSup T F U n] at k_maxcard
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s}) := by
      use k
      rw [mem_upperBounds]
      simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intros s h
      rw [← WithTop.coe_le_coe, k_maxcard]
      apply le_sSup
      simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      use s
    have h_nemp : (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s}).Nonempty := by
      use 0
      simp only [mem_image, mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact dynnet_by_empty T F U n
    rw [← WithTop.coe_sSup' h_bdda] at k_maxcard
    norm_cast at k_maxcard
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← k_maxcard, mem_image] at key
    simp only [mem_setOf_eq] at key
    exact key
  · rcases h with ⟨s, _, s_maxcard⟩
    rw [← s_maxcard]
    exact WithTop.coe_lt_top s.card

@[simp]
theorem maxcard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : Maxcard T ∅ U n = 0 := by
  unfold Maxcard
  rw [← bot_eq_zero, iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']

theorem empty_iff_maxcard_zero (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F = ∅ ↔ Maxcard T F U n = 0 := by
  refine Iff.intro (fun h ↦ by rw [h, maxcard_of_empty]) (fun h ↦ ?_)
  rw [eq_empty_iff_forall_not_mem]
  intros x x_F
  apply not_lt_of_le (α := ℕ∞) _ zero_lt_one
  rw [← h]
  apply le_of_eq_of_le (by rw [Finset.card_singleton, Nat.cast_one]) (le_iSup₂ {x} _)
  rw [Finset.coe_singleton]
  exact dynnet_by_singleton T U n x_F

theorem nonempty_iff_maxcard_pos (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F.Nonempty ↔ 1 ≤ Maxcard T F U n := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty]
  exact not_iff_not.2 (empty_iff_maxcard_zero T F U n)





theorem maxcard_time_zero_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    Maxcard T F U 0 = 1 := by
  apply le_antisymm (iSup₂_le _) ((nonempty_iff_maxcard_pos T F U 0).1 h)
  intro s ⟨_, s_net⟩
  simp [PairwiseDisjoint, ball] at s_net
  norm_cast
  apply Finset.card_le_one_iff_subsingleton_coe.2
  sorry
  replace s_net := Pairwise.Subsingleton s_net
  norm_cast
  rw [Finset.card_le_one]
  intros x x_in_s y y_in_s
  apply s_net x x_in_s y y_in_s
  use x
  unfold ball
  rw [dynamical_time_zero, preimage_univ, preimage_univ, inter_self]
  exact mem_univ x

theorem maxcard_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    Maxcard T F univ n = 1 := by
  sorry


theorem infinite_maxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n = ⊤ ↔
    ∀ k : ℕ, ∃ s : Finset X, IsDynamicalNetOf T F U n s ∧ k ≤ s.card := by
  apply Iff.intro <;> intro h
  · rw [maxcard_eq_sSup T F U n, sSup_eq_top] at h
    intro k
    specialize h (k : ℕ∞) (WithTop.coe_lt_top k)
    simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, exists_exists_and_eq_and,
      Nat.cast_lt] at h
    rcases h with ⟨s, s_net, s_k⟩
    use s
    exact ⟨s_net, le_of_lt s_k⟩
  · apply EReal.eq_top_iff_forall.2
    intro k
    specialize h (k+1)
    rcases h with ⟨s, s_net, s_card⟩
    apply lt_of_lt_of_le _ (card_le_maxcard s_net)
    rw [ENat.some_eq_coe, Nat.cast_lt]
    exact lt_of_lt_of_le (lt_add_one k) s_card






theorem net_maxcard_le_cover_mincard (T : X → X) (F : Set X) {U : Set (X × X)} (h : SymmetricRel U)
    (n : ℕ) :
    Maxcard T F U n ≤ Mincard T F U n := by
  rcases (eq_top_or_lt_top (Mincard T F U n)) with (h' | h')
  · exact h' ▸ le_top
  · rcases ((finite_mincard_iff T F U n).1 h') with ⟨t, t_cover, t_mincard⟩
    rw [← t_mincard]
    exact iSup₂_le (fun s s_net ↦ Nat.cast_le.2 (dynnet_card_le_dyncover_card h s_net t_cover))

theorem cover_mincard_comp_le_net_maxcard (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) (n : ℕ) :
    Mincard T F (U ○ U) n ≤ Maxcard T F U n := by
  classical
  rcases (eq_top_or_lt_top (Maxcard T F U n)) with (h | h)
  · exact h ▸ le_top
  · rcases ((finite_maxcard_iff T F U n).1 h) with ⟨s, s_net, s_maxcard⟩
    rw [← s_maxcard]
    apply mincard_le_card
    by_contra h
    unfold DynamicalCover.IsDynamicalCoverOf at h
    rcases not_subset.1 h with ⟨x, x_F, x_uncov⟩
    simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
    have t_larger_net : IsDynamicalNetOf T F U n (insert x s) := by
      apply And.intro (insert_subset x_F s_net.1)
      refine pairwiseDisjoint_insert.2 (And.intro s_net.2 (fun y y_s _ ↦ ?_))
      specialize x_uncov y y_s
      rcases ball_inter with ⟨w, w_in_ball_y, w_in_ball_z⟩
      simp only [Finset.mem_insert, t] at y_in_t z_in_t
      rcases y_in_t with (y_eq_x | y_in_s)
      · rw [y_eq_x]; rw [y_eq_x] at w_in_ball_y; clear y_eq_x y
        rcases z_in_t with (z_eq_x | z_in_s)
        · rw [z_eq_x]
        · exfalso
          apply x_not_covered
          simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop]
          use z
          constructor; exact z_in_s
          apply dynamical_of_comp_is_comp T U U n
          rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)] at w_in_ball_y
          exact mem_ball_comp w_in_ball_z w_in_ball_y
      · rcases z_in_t with (z_eq_x | z_in_s)
        · rw [z_eq_x]; rw [z_eq_x] at w_in_ball_z; clear z_eq_x z
          exfalso
          apply x_not_covered
          simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop]
          use y
          constructor; exact y_in_s
          apply dynamical_of_comp_is_comp T U U n
          rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)] at w_in_ball_z
          exact mem_ball_comp w_in_ball_y w_in_ball_z
        · apply s_net.2 y y_in_s z z_in_s
          use w
          exact ⟨w_in_ball_y, w_in_ball_z⟩
    apply not_le_of_lt _ (card_le_maxcard t_larger_net)
    rw [← s_maxcard]
    simp only [gt_iff_lt, Nat.cast_lt, t]
    apply lt_of_lt_of_eq (lt_add_one s.card)
    apply Eq.symm
    apply Finset.card_insert_of_not_mem
    intro x_in_s
    apply x_not_covered
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop]
    use x
    constructor
    · exact x_in_s
    · apply @ball_mono X idRel _ _ x
      · simp only [ball, mem_preimage, mem_idRel]
      · apply dynamical_of_rfl_is_rfl T _ n
        exact subset_trans U_rfl (left_subset_compRel U_rfl)










open ENNReal EReal

theorem log_maxcard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : log (Maxcard T ∅ U n) = ⊥ := by
  rw [maxcard_of_empty, ENat.toENNReal_zero, log_zero]

theorem log_maxcard_nonneg_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (Maxcard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (nonempty_iff_maxcard_pos T F U n).1 h

/-! ### Net entropy of uniformities -/

/--The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the largest (n, U)-dynamical net of F. Takes values in the space fo extended real numbers
[-∞,+∞]. This version uses a limsup.-/
noncomputable def NetEntropyInfUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.liminf fun n : ℕ ↦ log (Maxcard T F U n) / (n : ENNReal)

/--The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the largest (n, U)-dynamical net of F. Takes values in the space fo extended real numbers
[-∞,+∞]. This version uses a liminf.-/
noncomputable def NetEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.limsup fun n : ℕ ↦ log (Maxcard T F U n) / (n : ENNReal)

theorem NetEntropyInfUni_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ NetEntropyInfUni T F U) :=
  fun U V U_V ↦ Filter.liminf_le_liminf <| Filter.eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (maxcard_antitone_uni T F n U_V))

theorem NetEntropySupUni_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ NetEntropySupUni T F U) :=
  fun U V U_V ↦ Filter.limsup_le_limsup <| Filter.eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (maxcard_antitone_uni T F n U_V))

theorem NetEntropyInfUni_le_NetEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :
    NetEntropyInfUni T F U ≤ NetEntropySupUni T F U :=
  Filter.liminf_le_limsup

@[simp]
theorem NetEntropySupUni_of_empty {T : X → X} {U : Set (X × X)} : NetEntropySupUni T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in Filter.atTop, log (Maxcard T ∅ U n) / n = ⊥
  · unfold NetEntropySupUni
    exact Filter.limsup_congr h ▸ Filter.limsup_const ⊥
  · simp only [maxcard_of_empty, ENat.toENNReal_zero, log_zero, Filter.eventually_atTop]
    use 1
    exact fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (Ereal_natCast_ne_top n)

@[simp]
theorem NetEntropyInfUni_of_empty {T : X → X} {U : Set (X × X)} : NetEntropyInfUni T ∅ U = ⊥ :=
  eq_bot_mono (NetEntropyInfUni_le_NetEntropySupUni T ∅ U) NetEntropySupUni_of_empty

theorem nonneg_NetEntropyInfUni_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    0 ≤ NetEntropyInfUni T F U := by
  sorry
  /-le_trans (le_iInf fun n ↦ EReal.div_nonneg (log_mincard_nonneg_of_nonempty T h U n)
    (Nat.cast_nonneg' n)) Filter.iInf_le_liminf-/

theorem nonneg_NetEntropySupUni_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    0 ≤ NetEntropySupUni T F U :=
  le_trans (nonneg_NetEntropyInfUni_of_nonempty T h U) (NetEntropyInfUni_le_NetEntropySupUni T F U)

theorem NetEntropyInfUni_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    NetEntropyInfUni T F univ = 0 := by
  simp [NetEntropyInfUni, maxcard_by_univ_of_nonempty T h]

theorem NetEntropySupUni_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    NetEntropySupUni T F univ = 0 := by
  simp [NetEntropySupUni, maxcard_by_univ_of_nonempty T h]




theorem NetEntropyInfUni_le_CoverEntropyInfUni (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : SymmetricRel U) :
    NetEntropyInfUni T F U ≤ CoverEntropyInfUni T F U := by
  apply liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply div_left_mono
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_le_cover_mincard T F h n

theorem cover_entropy_comp_le_net_entropy (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
    CoverEntropyInfUni T F (U ○ U) ≤ NetEntropyInfUni T F U := by
  apply liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_comp_le_net_maxcard T F U_rfl U_symm n

theorem net_entropy'_le_cover_entropy' (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : SymmetricRel U) :
    NetEntropySupUni T F U ≤ CoverEntropySupUni T F U := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_le_cover_mincard T F h n

theorem cover_entropy'_comp_le_net_entropy' (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
  CoverEntropySupUni T F (U ○ U) ≤ NetEntropySupUni T F U := by
  apply limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_comp_le_net_maxcard T F U_rfl U_symm n

/-! ### Net entropy -/

/-- The entropy of T restricted to F, obtained by taking the supremum over uniformity neighbourhoods.
Note that this supremum is approached by taking small neighbourhoods.-/
noncomputable def NetEntropyInf [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, NetEntropyInfUni T F U

/-- An alternative definition of the entropy of T restricted to F, using a liminf instead of
a limsup.-/
noncomputable def NetEntropySup [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, NetEntropySupUni T F U

theorem NetEntropyInf_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @NetEntropyInf X u T F := by
  intro u₁ u₂ h
  refine iSup₂_mono' (fun U U_uni₂ ↦ ?_)
  use U, (Filter.le_def.1 h) U U_uni₂

theorem NetEntropySup_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @NetEntropySup X u T F := by
  intro u₁ u₂ h
  refine iSup₂_mono' (fun U U_uni₂ ↦ ?_)
  use U, (Filter.le_def.1 h) U U_uni₂

variable [UniformSpace X]

theorem NetEntropyInfUni_le_NetEntropyInf [UniformSpace X] (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    NetEntropyInfUni T F U ≤ NetEntropyInf T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ NetEntropyInfUni T F U) U h

theorem NetEntropySupUni_le_NetEntropySup [UniformSpace X] (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    NetEntropySupUni T F U ≤ NetEntropySup T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ NetEntropySupUni T F U) U h

theorem NetEntropyInf_of_basis {ι : Sort*} [UniformSpace X] {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    NetEntropyInf T F = ⨆ (i : ι) (_ : p i), NetEntropyInfUni T F (s i) := by
  apply le_antisymm
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    rcases (Filter.HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
    apply le_trans (NetEntropyInfUni_antitone_uni T F si_U)
    apply le_iSup₂ i h_i
  · refine iSup₂_mono' (fun i h_i ↦ ?_)
    use s i, Filter.HasBasis.mem_of_mem h h_i

theorem NetEntropySup_of_basis {ι : Sort*} [UniformSpace X] {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    NetEntropySup T F = ⨆ (i : ι) (_ : p i), NetEntropySupUni T F (s i) := by
  apply le_antisymm
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    rcases (Filter.HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
    apply le_trans (NetEntropySupUni_antitone_uni T F si_U)
    apply le_iSup₂ i h_i
  · refine iSup₂_mono' (fun i h_i ↦ ?_)
    use s i, Filter.HasBasis.mem_of_mem h h_i

theorem NetEntropyInf_le_NetEntropySup (T : X → X) (F : Set X) :
    NetEntropyInf T F ≤ NetEntropySup T F :=
  iSup₂_mono (fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ NetEntropyInfUni_le_NetEntropySupUni T F U)

@[simp]
theorem NetEntropyInf_of_empty {T : X → X} : NetEntropyInf T ∅ = ⊥ := by
  simp only [NetEntropyInf, NetEntropyInfUni_of_empty, iSup_bot]

@[simp]
theorem NetEntropySup_of_empty {T : X → X} : NetEntropySup T ∅ = ⊥ := by
  simp only [NetEntropySup, NetEntropySupUni_of_empty, iSup_bot]

theorem nonneg_NetEntropyInf_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ NetEntropyInf T F :=
  le_of_eq_of_le (Eq.symm (NetEntropyInfUni_by_univ_of_nonempty T h))
    (NetEntropyInfUni_le_NetEntropyInf T F Filter.univ_mem)

theorem nonneg_NetEntropySup_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ NetEntropySup T F :=
  le_trans (nonneg_NetEntropyInf_of_nonempty T h) (NetEntropyInf_le_NetEntropySup T F)






theorem NetEntropyInf_eq_CoverEntropyInf (T : X → X) (F : Set X) :
    NetEntropyInf T F = CoverEntropyInf T F := by
  apply le_antisymm
  · apply iSup₂_le
    intro U U_uni
    apply le_trans (NetEntropyInfUni_antitone_uni T F (symmetrizeRel_subset_self U)) _
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact NetEntropyInfUni_le_CoverEntropyInfUni T F (symmetric_symmetrizeRel U)
  · apply iSup₂_le
    intro U U_uni
    rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply le_trans (CoverEntropyInfUni_antitone_uni T F V_comp_U)
      <| le_iSup₂_of_le V V_uni
      <| cover_entropy_comp_le_net_entropy T F (refl_le_uniformity V_uni) V_symm

theorem net_entropy'_eq_cover_entropy' (T : X → X) (F : Set X) :
    Entropy' T F = DynamicalCover.Entropy' T F := by
  apply le_antisymm
  · apply iSup₂_le
    intro U U_uni
    apply le_trans (net_entropy'_antitone_uni T F (symmetrizeRel_subset_self U)) _
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact net_entropy'_le_cover_entropy' T F (symmetric_symmetrizeRel U)
  · apply iSup₂_le
    intro U U_uni
    rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply le_trans (DynamicalCover.cover_entropy'_antitone_uni T F V_comp_U)
      <| le_iSup₂_of_le V V_uni
      <| cover_entropy'_comp_le_net_entropy' T F (refl_le_uniformity V_uni) V_symm

theorem net_entropy_eq_cover_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy T F = DynamicalCover.Entropy' T F :=
  Eq.trans (net_entropy_eq_cover_entropy T F) (DynamicalCover.entropy_eq_entropy' T h)

theorem net_entropy'_eq_cover_entropy (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy' T F = DynamicalCover.Entropy T F :=
  Eq.trans (net_entropy'_eq_cover_entropy' T F) (Eq.symm (DynamicalCover.entropy_eq_entropy' T h))

theorem net_entropy_eq_net_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy T F = Entropy' T F :=
  Eq.trans (net_entropy_eq_cover_entropy' T h) (Eq.symm (net_entropy'_eq_cover_entropy' T F))

end DynamicalNet

#lint
