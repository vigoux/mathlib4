/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Dynamics.TopologicalEntropy.DynamicalUniformity

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

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

## Main definitions
- `IsDynamicalCoverOf`: property that dynamical balls centered on a subset `s` cover a subset `F`.
- `Mincard`: minimal cardinal of a dynamical cover. Takes values in `ℕ∞`.
- `CoverEntropyInfUni`/`CoverEntropySupUni`: exponential growth of `Mincard`. The former is
defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `CoverEntropyInf`/`CoverEntropySup`: supremum of `CoverEntropyInfUni`/`CoverEntropySupUni` over
all uniformities (or limit as the uniformity goes to the diagonal). These are Bowen-Dinaburg's
versions of the topological entropy with covers. Take values in `EReal`.

## Tags
cover, entropy

## TODO
The most painful part of many manipulations involving topological entropy is going from `Mincard`
to `CoverEntropyInfUni`/`CoverEntropySupUni`. It involves a logarithm, a division, a
`liminf`/`limsup`, and multiple coercions. The best thing to do would be to write a file on
"exponential growth" to make a clean pathway from estimates on `Mincard` to estimates on
`CoverEntropy`/`CoverEntropy'`. It would also be useful in other similar contexts.

Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace DynamicalCover

open DynamicalUniformity Set Uniformity UniformSpace

variable {X : Type*}

open EReal

theorem Ereal_tendsto_const_div_atTop_nhds_zero_nat {x : EReal} (h : x ≠ ⊥) (h' : x ≠ ⊤) :
    Filter.atTop.Tendsto (fun n : ℕ ↦ x / n) (nhds 0) := by
  have : (fun n : ℕ ↦ x / n) = fun n : ℕ ↦ ((x.toReal / n : ℝ) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div x.toReal n]
  rw [this, ← EReal.coe_zero, EReal.tendsto_coe]
  exact tendsto_const_div_atTop_nhds_zero_nat x.toReal

/-! ### Dynamical covers -/

/-- Given a subset `F`, a uniform neighborhood `U` and an integer `n`, a subset `s` is a `(U, n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an orbit of length `n`
of a point in `s`.-/
def IsDynamicalCoverOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  F ⊆ ⋃ x ∈ s, ball x (DynamicalUni T U n)

theorem dyncover_monotone_time {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ}
    (m_n : m ≤ n) {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F U m s := by
    exact Subset.trans (c := ⋃ x ∈ s, ball x (DynamicalUni T U m)) h
      (iUnion₂_mono fun x _ ↦ ball_mono (dynamical_uni_antitone_time T U m_n) x)

theorem dyncover_antitone_uni {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F V n s := by
  exact Subset.trans (c := ⋃ x ∈ s, ball x (DynamicalUni T V n)) h
    (iUnion₂_mono fun x _ ↦ ball_mono (dynamical_uni_monotone_uni T n U_V) x)

theorem empty_dyncover_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    IsDynamicalCoverOf T ∅ U n ∅ := by
  simp only [IsDynamicalCoverOf, empty_subset]

theorem nonempty_dyncover_of_nonempty {T : X → X} {F : Set X} (h : F.Nonempty) {U : Set (X × X)}
    {n : ℕ} {s : Set X} (h' : IsDynamicalCoverOf T F U n s) :
    s.Nonempty := by
  rcases nonempty_biUnion.1 (Nonempty.mono h' h) with ⟨x, x_s, _⟩
  exact nonempty_of_mem x_s

theorem dyncover_time_zero (T : X → X) (F : Set X) (U : Set (X × X)) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F U 0 s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, not_lt_zero', Prod.map_iterate,
    iInter_of_empty, iInter_univ, preimage_univ]
  rcases h with ⟨x, x_s⟩
  exact subset_iUnion₂_of_subset x x_s (subset_univ F)

theorem dyncover_by_univ (T : X → X) (F : Set X) (n : ℕ) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F univ n s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, Prod.map_iterate, preimage_univ,
    iInter_univ, iUnion_coe_set]
  rcases h with ⟨x, x_s⟩
  exact subset_iUnion₂_of_subset x x_s (subset_univ F)

/-This lemma is the first step in a submultiplicative-like property of `Mincard`, with far-reaching
  consequence such as explicit bounds for the topological entropy (`CoverEntropyInfUni_le_card_div`)
  and an equality between two notions of topological entropy
  (`CoverEntropyInf_eq_CoverEntropySup_of_inv`).-/
theorem dyncover_iterate {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : SymmetricRel U) {m : ℕ} (n : ℕ) {s : Finset X} (h : IsDynamicalCoverOf T F U m s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F (U ○ U) (m * n) t ∧ t.card ≤ s.card ^ n := by
  classical
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · use ∅; simp [empty_dyncover_of_empty]
  have _ : Nonempty X := nonempty_of_exists F_nemp
  have s_nemp := nonempty_dyncover_of_nonempty F_nemp h
  rcases F_nemp with ⟨x, x_F⟩
  rcases m.eq_zero_or_pos with (rfl | m_pos)
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact And.intro (dyncover_time_zero T F (U ○ U) (singleton_nonempty x))
      <| one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n
  have :
    ∀ β : Fin n → s, ∃ y : X,
      (⋂ k : Fin n, T^[m * k] ⁻¹' ball (β k) (DynamicalUni T U m)) ⊆
      ball y (DynamicalUni T (U ○ U) (m * n)) := by
    intro t
    rcases (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (DynamicalUni T U m)).eq_empty_or_nonempty
      with (inter_empt | inter_nemp)
    · rw [inter_empt]
      use x
      exact empty_subset _
    · rcases inter_nemp with ⟨y, y_int⟩
      use y
      intro z z_int
      simp only [ball, DynamicalUni, Prod.map_iterate, mem_preimage, mem_iInter,
        Prod.map_apply] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball U_symm y_int z_int
  choose! dyncover h_dyncover using this
  let sn := range dyncover
  have _ := fintypeRange dyncover
  use sn.toFinset
  constructor
  · rw [Finset.coe_nonempty] at s_nemp
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nemp
    intro y y_F
    have key : ∀ k : Fin n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (DynamicalUni T U m) := by
      intro k
      have := h (MapsTo.iterate F_inv (m * k) y_F)
      simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at this
      rcases this with ⟨z, z_s, hz⟩
      use ⟨z, z_s⟩
      exact hz
    choose! t ht using key
    specialize h_dyncover t
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, toFinset_range,
      Finset.mem_image, Finset.mem_univ, true_and, exists_prop, exists_exists_eq_and, sn]
    simp only [mem_preimage, Subtype.forall, Finset.mem_range] at ht
    use dyncover t
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_range, exists_apply_eq_apply,
      true_and]
    apply h_dyncover
    simp only [mem_iInter, mem_preimage, Finset.mem_range]
    exact ht
  · rw [toFinset_card]
    apply le_trans (Fintype.card_range_le dyncover)
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

theorem exists_dyncover_of_compact_continuous [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {F : Set X} (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s := by
  have uni_ite := dynamical_uni_of_uni h U_uni n
  let open_cover := fun x : X ↦ ball x (DynamicalUni T U n)
  have := IsCompact.elim_nhds_subcover F_comp open_cover (fun (x : X) _ ↦ ball_mem_nhds x uni_ite)
  rcases this with ⟨s, _, s_cover⟩
  use s, s_cover

theorem exists_dyncover_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  let open_cover := fun x : X ↦ ball x V
  have := IsCompact.elim_nhds_subcover F_comp open_cover (fun (x : X) _ ↦ ball_mem_nhds x V_uni)
  rcases this with ⟨s, _, s_cover⟩
  have : IsDynamicalCoverOf T F V 1 s := by
    intro x x_F
    specialize s_cover x_F
    simp only [mem_iUnion, exists_prop] at s_cover
    rcases s_cover with ⟨y, y_s, _⟩
    simp only [DynamicalUni, Nat.lt_one_iff, iInter_iInter_eq_left, Function.iterate_zero,
      Prod.map_id, preimage_id_eq, id_eq, mem_iUnion]
    use y, y_s
  rcases dyncover_iterate F_inv V_symm n this with ⟨t, t_dyncover, t_card⟩
  rw [one_mul n] at t_dyncover
  use t
  exact dyncover_antitone_uni V_U t_dyncover

/-! ### Minimal cardinal of dynamical covers -/

/-- The smallest cardinal of a `(U, n)`-dynamical cover of `F`. Takes values in `ℕ∞`, and is infinite
if and only if `F` admits no finite dynamical cover.-/
noncomputable def Mincard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynamicalCoverOf T F U n s), (s.card : ℕ∞)

theorem mincard_eq_sInf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n
    = sInf (WithTop.some '' (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s})) := by
  unfold Mincard
  rw [← image_comp, sInf_image]
  simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]

theorem mincard_le_card {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    Mincard T F U n ≤ s.card := iInf₂_le s h

theorem mincard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ Mincard T F U n) := by
  intros m n m_n
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F U m]
  apply sInf_le_sInf
  apply image_subset
  apply image_subset
  exact fun s ↦ dyncover_monotone_time m_n

theorem mincard_antitone_uni (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X×X) ↦ Mincard T F U n) := by
  intros U V U_V
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F V n]
  apply sInf_le_sInf
  apply image_subset
  apply image_subset
  exact fun s ↦ dyncover_antitone_uni U_V

theorem finite_mincard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s ∧ s.card = Mincard T F U n := by
  apply Iff.intro _ (fun ⟨s, _, s_mincard⟩ ↦ Eq.symm s_mincard ▸ WithTop.coe_lt_top s.card)
  rw [mincard_eq_sInf T F U n]
  intro mincard_fin
  rcases WithTop.ne_top_iff_exists.1 (ne_of_lt mincard_fin) with ⟨k, k_mincard⟩
  rw [← k_mincard]
  simp only [ENat.some_eq_coe, Nat.cast_inj]
  have h_nemp : (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp only [ENat.some_eq_coe, h, image_empty, sInf_empty, lt_self_iff_false] at mincard_fin
  have h_bddb : BddBelow (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}) := by
    use 0
    simp only [lowerBounds, mem_setOf_eq, zero_le, implies_true]
  rw [← WithTop.coe_sInf' h_nemp h_bddb] at k_mincard
  norm_cast at k_mincard
  have := Nat.sInf_mem h_nemp
  rw [← k_mincard] at this
  simp only [mem_image, mem_setOf_eq] at this
  exact this

@[simp]
theorem mincard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : Mincard T ∅ U n = 0 := by
  apply le_antisymm (sInf_le _) (zero_le (Mincard T ∅ U n))
  use ∅
  simp [IsDynamicalCoverOf]

theorem empty_iff_mincard_zero (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F = ∅ ↔ Mincard T F U n = 0 := by
  apply Iff.intro fun F_empt ↦ by rw [F_empt, mincard_of_empty]
  intro mincard_zero
  have := finite_mincard_iff T F U n
  rw [mincard_zero] at this
  simp only [ENat.zero_lt_top, IsDynamicalCoverOf, Finset.mem_coe, Nat.cast_eq_zero,
    Finset.card_eq_zero, exists_eq_right, Finset.not_mem_empty, iUnion_of_empty, iUnion_empty,
    true_iff] at this
  exact eq_empty_iff_forall_not_mem.2 this

theorem nonempty_iff_mincard_pos (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F.Nonempty ↔ 1 ≤ Mincard T F U n := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty, not_iff_not]
  exact empty_iff_mincard_zero T F U n

theorem mincard_time_zero_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    Mincard T F U 0 = 1 := by
  apply le_antisymm _ ((nonempty_iff_mincard_pos T F U 0).1 h)
  rcases h with ⟨x, _⟩
  have := (dyncover_time_zero T F U (singleton_nonempty x))
  rw [← Finset.coe_singleton] at this
  apply le_of_le_of_eq (mincard_le_card this)
  rw [Finset.card_singleton, Nat.cast_one]

theorem mincard_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    Mincard T F univ n = 1 := by
  apply le_antisymm _ ((nonempty_iff_mincard_pos T F univ n).1 h)
  rcases h with ⟨x, _⟩
  have := (dyncover_by_univ T F n (singleton_nonempty x))
  rw [← Finset.coe_singleton] at this
  apply le_of_le_of_eq (mincard_le_card this)
  rw [Finset.card_singleton, Nat.cast_one]

theorem mincard_iterate {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : SymmetricRel U) (m n : ℕ) :
    Mincard T F (U ○ U) (m * n) ≤ Mincard T F U m ^ n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · rw [mincard_of_empty]; exact zero_le _
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [mul_zero, mincard_time_zero_of_nonempty T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (Mincard T F U m) with (h | h)
  · exact h ▸ le_of_le_of_eq (le_top (α := ℕ∞)) (Eq.symm (ENat.top_pow n_pos))
  · rcases (finite_mincard_iff T F U m).1 h with ⟨s, s_cover, s_mincard⟩
    rcases dyncover_iterate F_inv U_symm n s_cover with ⟨t, t_cover, t_le_sn⟩
    rw [← s_mincard]
    exact le_trans (mincard_le_card t_cover) (WithTop.coe_le_coe.2 t_le_sn)

theorem mincard_upper_bound {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : SymmetricRel U) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    Mincard T F (U ○ U) n ≤ Mincard T F U m ^ (n / m + 1) :=
  le_trans (mincard_monotone_time T F (U ○ U) (le_of_lt (Nat.lt_mul_div_succ n m_pos)))
    (mincard_iterate F_inv U_symm m (n / m + 1))

theorem finite_mincard_of_compact_continuous [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {F : Set X} (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    Mincard T F U n < ⊤ := by
  rcases exists_dyncover_of_compact_continuous h F_comp U_uni n with ⟨s, s_cover⟩
  exact lt_of_le_of_lt (mincard_le_card s_cover) (WithTop.coe_lt_top s.card)

theorem finite_mincard_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    Mincard T F U n < ⊤ := by
  rcases exists_dyncover_of_compact_inv F_inv F_comp U_uni n with ⟨s, s_cover⟩
  exact lt_of_le_of_lt (mincard_le_card s_cover) (WithTop.coe_lt_top s.card)

theorem dyncover_elim {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F U n t ∧ t.card ≤ s.card
    ∧ ∀ x ∈ t, ((ball x (DynamicalUni T U n)) ∩ F).Nonempty := by
  classical
  use Finset.filter (fun x : X ↦ ((ball x (DynamicalUni T U n)) ∩ F).Nonempty) s
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  apply And.intro _ (Finset.card_mono (Finset.filter_subset _ s))
  intros y y_F
  specialize h y_F
  simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at h
  rcases h with ⟨z, z_s, y_Bz⟩
  simp only [coe_setOf, mem_setOf_eq, mem_iUnion, Subtype.exists, exists_prop]
  use z
  exact ⟨⟨z_s, nonempty_of_mem ⟨y_Bz, y_F⟩⟩, y_Bz⟩

theorem minimal_dyncover_ball_inter {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) (h' : s.card = Mincard T F U n) :
    ∀ x ∈ s, (F ∩ ball x (DynamicalUni T U n)).Nonempty := by
  classical
  by_contra hypo
  push_neg at hypo
  rcases hypo with ⟨x, x_s, ball_empt⟩
  let t := Finset.erase s x
  have t_smaller_cover : IsDynamicalCoverOf T F U n t := by
    intro y y_F
    specialize h y_F
    simp only [Finset.mem_coe, mem_iUnion, exists_prop] at h
    rcases h with ⟨z, z_s, hz⟩
    simp only [Finset.coe_erase, mem_diff, Finset.mem_coe, mem_singleton_iff, mem_iUnion,
      exists_prop, t]
    use z
    refine And.intro (And.intro z_s fun z_x ↦ ?_) hz
    rw [z_x] at hz
    apply not_mem_empty y
    rw [← ball_empt]
    exact mem_inter y_F hz
  apply not_lt_of_le (mincard_le_card t_smaller_cover)
  rw [← h']
  norm_cast
  exact Finset.card_erase_lt_of_mem x_s

open ENNReal EReal

theorem log_mincard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    log (Mincard T ∅ U n) = ⊥ := by
  rw [mincard_of_empty, ENat.toENNReal_zero, log_zero]

theorem log_mincard_nonneg_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X))
    (n : ℕ) :
    0 ≤ log (Mincard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (nonempty_iff_mincard_pos T F U n).1 h

theorem log_mincard_iterate {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : SymmetricRel U) (m : ℕ) {n : ℕ} (n_pos : 0 < n) :
    log (Mincard T F (U ○ U) (m * n)) / n ≤ log (Mincard T F U m) := by
  apply (EReal.div_le_iff_le_mul (b := n) (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)).2
  rw [← log_pow, StrictMono.le_iff_le log_strictMono]
  nth_rw 2 [← ENat.toENNRealRingHom_apply]
  rw [← RingHom.map_pow ENat.toENNRealRingHom _ n, ENat.toENNRealRingHom_apply, ENat.toENNReal_le]
  exact mincard_iterate F_inv U_symm m n

theorem log_mincard_upper_bound {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : SymmetricRel U) {m n : ℕ} (m_pos : 0 < m) (n_pos : 0 < n) :
    log (Mincard T F (U ○ U) n) / n ≤ log (Mincard T F U m) / m + log (Mincard T F U m) / n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · rw [mincard_of_empty, ENat.toENNReal_zero, log_zero,
      bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)]
    exact bot_le
  have h_nm : (0 : EReal) ≤ (n / m : ℕ) := Nat.cast_nonneg' (n / m)
  have h_log := log_mincard_nonneg_of_nonempty T F_nemp U m
  have n_div_n := EReal.div_self (natCast_ne_bot n) (natCast_ne_top n)
    (ne_of_gt (Nat.cast_pos'.2 n_pos))
  apply le_trans <| div_le_div_right_of_nonneg (le_of_lt (Nat.cast_pos'.2 n_pos))
    (log_monotone (ENat.toENNReal_le.2 (mincard_upper_bound F_inv U_symm m_pos n)))
  rw [ENat.toENNReal_pow, log_pow, Nat.cast_add, Nat.cast_one, right_distrib_of_nonneg h_nm
    zero_le_one, one_mul, div_right_distrib_of_nonneg (Left.mul_nonneg h_nm h_log) h_log, mul_comm,
    ← EReal.mul_div, div_eq_mul_inv _ (m : EReal)]
  apply add_le_add_right (mul_le_mul_of_nonneg_left _ h_log)
  apply le_of_le_of_eq <| div_le_div_right_of_nonneg (le_of_lt (Nat.cast_pos'.2 n_pos))
    (natCast_div_le n m)
  rw [EReal.div_div, mul_comm, ← EReal.div_div, n_div_n, one_div (m : EReal)]

/-! ### Cover entropy of uniformities -/

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers
[-∞,+∞]. The first version uses a liminf.-/
noncomputable def CoverEntropyInfUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.liminf fun n : ℕ ↦ log (Mincard T F U n) / n

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers
[-∞,+∞]. The second version uses a limsup.-/
noncomputable def CoverEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.limsup fun n : ℕ ↦ log (Mincard T F U n) / n

theorem CoverEntropyInfUni_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ CoverEntropyInfUni T F U) :=
  fun U V U_V ↦ Filter.liminf_le_liminf <| Filter.eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (mincard_antitone_uni T F n U_V))

theorem CoverEntropySupUni_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ CoverEntropySupUni T F U) :=
  fun U V U_V ↦ Filter.limsup_le_limsup <| Filter.eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (mincard_antitone_uni T F n U_V))

theorem CoverEntropyInfUni_le_CoverEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :
    CoverEntropyInfUni T F U ≤ CoverEntropySupUni T F U := Filter.liminf_le_limsup

@[simp]
theorem CoverEntropySupUni_of_empty {T : X → X} {U : Set (X × X)} :
    CoverEntropySupUni T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in Filter.atTop, log (Mincard T ∅ U n) / n = ⊥
  · unfold CoverEntropySupUni
    exact Filter.limsup_congr h ▸ Filter.limsup_const ⊥
  · simp only [mincard_of_empty, ENat.toENNReal_zero, log_zero, Filter.eventually_atTop]
    use 1
    exact fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)

@[simp]
theorem CoverEntropyInfUni_of_empty {T : X → X} {U : Set (X × X)} :
    CoverEntropyInfUni T ∅ U = ⊥ :=
  eq_bot_mono (CoverEntropyInfUni_le_CoverEntropySupUni T ∅ U) CoverEntropySupUni_of_empty

theorem nonneg_CoverEntropyInfUni_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    0 ≤ CoverEntropyInfUni T F U :=
  le_trans (le_iInf fun n ↦ EReal.div_nonneg (log_mincard_nonneg_of_nonempty T h U n)
    (Nat.cast_nonneg' n)) Filter.iInf_le_liminf

theorem nonneg_CoverEntropySupUni_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    0 ≤ CoverEntropySupUni T F U :=
  le_trans (nonneg_CoverEntropyInfUni_of_nonempty T h U)
    (CoverEntropyInfUni_le_CoverEntropySupUni T F U)

theorem CoverEntropyInfUni_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    CoverEntropyInfUni T F univ = 0 := by
  simp [CoverEntropyInfUni, mincard_by_univ_of_nonempty T h]

theorem CoverEntropySupUni_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    CoverEntropySupUni T F univ = 0 := by
  simp [CoverEntropySupUni, mincard_by_univ_of_nonempty T h]

theorem CoverEntropyInfUni_le_log_mincard_div {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : SymmetricRel U) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropyInfUni T F (U ○ U) ≤ log (Mincard T F U n) / n := by
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  use (max 1 N) * n
  constructor
  · rcases eq_zero_or_pos N with (rfl | N_pos)
    · exact zero_le ((max 1 0) * n)
    · rw [max_eq_right (Nat.one_le_of_lt N_pos)]
      nth_rw 2 [← mul_one N]
      exact Nat.mul_le_mul_left N (Nat.one_le_of_lt n_pos)
  · have := log_mincard_iterate F_inv U_symm n (lt_of_lt_of_le zero_lt_one (le_max_left 1 N))
    rw [mul_comm n (max 1 N)] at this
    apply le_of_eq_of_le _ (div_le_div_right_of_nonneg (Nat.cast_nonneg' n) this)
    rw [EReal.div_div]
    congr
    exact natCast_mul (max 1 N) n

theorem CoverEntropyInfUni_le_card_div {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : SymmetricRel U) {n : ℕ} (n_pos : 0 < n) {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    CoverEntropyInfUni T F (U ○ U) ≤ log s.card / n := by
  apply le_trans (CoverEntropyInfUni_le_log_mincard_div F_inv U_symm n_pos)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  apply log_monotone
  norm_cast
  exact mincard_le_card h

theorem CoverEntropySupUni_le_log_mincard_div {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : SymmetricRel U) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropySupUni T F (U ○ U) ≤ log (Mincard T F U n) / n := by
  rcases eq_or_ne (log (Mincard T F U n)) ⊥ with (logm_bot | logm_nneg)
  · rw [log_eq_bot_iff, ← ENat.toENNReal_zero, ENat.toENNReal_coe_eq_iff,
      ← empty_iff_mincard_zero T F U n] at logm_bot
    simp [logm_bot]
  rcases eq_or_ne (log (Mincard T F U n)) ⊤ with (logm_top | logm_fin)
  · rw [logm_top, top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)]
    exact le_top
  let u := fun _ : ℕ ↦ log (Mincard T F U n) / n
  let v := fun m : ℕ ↦ log (Mincard T F U n) / m
  let w := fun m : ℕ ↦ log (Mincard T F (U ○ U) m) / m
  have key : w ≤ᶠ[Filter.atTop] u + v := by
    apply Filter.eventually_atTop.2
    use 1
    simp only [Pi.add_apply, w, u, v]
    intro m m_pos
    exact log_mincard_upper_bound F_inv U_symm n_pos m_pos
  apply le_trans (limsup_le_limsup key)
  suffices h : Filter.atTop.limsup v = 0
  · have := @limsup_add_le_add_limsup ℕ Filter.atTop u v
    rw [h, add_zero] at this
    specialize this (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)
    exact le_of_le_of_eq this (Filter.limsup_const (log (Mincard T F U n) / n))
  exact Filter.Tendsto.limsup_eq (Ereal_tendsto_const_div_atTop_nhds_zero_nat logm_nneg logm_fin)

theorem CoverEntropySupUni_le_CoverEntropyInfUni {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : SymmetricRel U) :
    CoverEntropySupUni T F (U ○ U) ≤ CoverEntropyInfUni T F U := by
  apply (Filter.le_liminf_of_le)
  apply Filter.eventually_atTop.2
  use 1
  exact fun m m_pos ↦ CoverEntropySupUni_le_log_mincard_div F_inv U_symm m_pos

theorem finite_CoverEntropyInfUni_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) :
    CoverEntropyInfUni T F U < ⊤ := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  rcases exists_dyncover_of_compact_inv F_inv F_comp V_uni 1 with ⟨s, s_cover⟩
  apply lt_of_le_of_lt (CoverEntropyInfUni_antitone_uni T F V_U)
  apply lt_of_le_of_lt (CoverEntropyInfUni_le_card_div F_inv V_symm zero_lt_one s_cover)
  rw [Nat.cast_one, div_one, log_lt_top_iff, ← ENat.toENNReal_top]
  norm_cast
  exact Ne.lt_top (ENat.coe_ne_top (Finset.card s))

theorem finite_CoverEntropySupUni_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) :
    CoverEntropySupUni T F U < ⊤ := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  exact lt_of_le_of_lt (CoverEntropySupUni_antitone_uni T F V_U)
    <| lt_of_le_of_lt (CoverEntropySupUni_le_CoverEntropyInfUni F_inv V_symm)
    <| finite_CoverEntropyInfUni_of_compact_inv F_inv F_comp V_uni

/-! ### Cover entropy -/

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum over uniformities.
Note that this supremum is approached by taking small uniformities. This version uses a `liminf`.-/
noncomputable def CoverEntropyInf [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, CoverEntropyInfUni T F U

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum over uniformities.
Note that this supremum is approached by taking small uniformities. This version uses a `limsup`.-/
noncomputable def CoverEntropySup [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, CoverEntropySupUni T F U

theorem CoverEntropyInf_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @CoverEntropyInf X u T F := by
  intro u₁ u₂ h
  refine iSup₂_mono' (fun U U_uni₂ ↦ ?_)
  use U, (Filter.le_def.1 h) U U_uni₂

theorem CoverEntropySup_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @CoverEntropySup X u T F := by
  intro u₁ u₂ h
  refine iSup₂_mono' (fun U U_uni₂ ↦ ?_)
  use U, (Filter.le_def.1 h) U U_uni₂

variable [UniformSpace X]

theorem CoverEntropyInfUni_le_CoverEntropyInf [UniformSpace X] (T : X → X) (F : Set X)
    {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    CoverEntropyInfUni T F U ≤ CoverEntropyInf T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ CoverEntropyInfUni T F U) U h

theorem CoverEntropySupUni_le_CoverEntropySup [UniformSpace X] (T : X → X) (F : Set X)
    {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    CoverEntropySupUni T F U ≤ CoverEntropySup T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ CoverEntropySupUni T F U) U h

theorem CoverEntropyInf_of_basis {ι : Sort*} [UniformSpace X] {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    CoverEntropyInf T F = ⨆ (i : ι) (_ : p i), CoverEntropyInfUni T F (s i) := by
  apply le_antisymm
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    rcases (Filter.HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
    apply le_trans (CoverEntropyInfUni_antitone_uni T F si_U)
    apply le_iSup₂ i h_i
  · refine iSup₂_mono' (fun i h_i ↦ ?_)
    use s i, Filter.HasBasis.mem_of_mem h h_i

theorem CoverEntropySup_of_basis {ι : Sort*} [UniformSpace X] {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    CoverEntropySup T F = ⨆ (i : ι) (_ : p i), CoverEntropySupUni T F (s i) := by
  apply le_antisymm
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    rcases (Filter.HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
    apply le_trans (CoverEntropySupUni_antitone_uni T F si_U)
    apply le_iSup₂ i h_i
  · refine iSup₂_mono' (fun i h_i ↦ ?_)
    use s i, Filter.HasBasis.mem_of_mem h h_i

theorem CoverEntropyInf_le_CoverEntropySup (T : X → X) (F : Set X) :
    CoverEntropyInf T F ≤ CoverEntropySup T F :=
  iSup₂_mono (fun (U : Set (X × X)) (_ : U ∈ uniformity X)
    ↦ CoverEntropyInfUni_le_CoverEntropySupUni T F U)

@[simp]
theorem CoverEntropyInf_of_empty {T : X → X} : CoverEntropyInf T ∅ = ⊥ := by
  simp only [CoverEntropyInf, CoverEntropyInfUni_of_empty, iSup_bot]

@[simp]
theorem CoverEntropySup_of_empty {T : X → X} : CoverEntropySup T ∅ = ⊥ := by
  simp only [CoverEntropySup, CoverEntropySupUni_of_empty, iSup_bot]

theorem nonneg_CoverEntropyInf_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ CoverEntropyInf T F :=
  le_of_eq_of_le (Eq.symm (CoverEntropyInfUni_by_univ_of_nonempty T h))
    (CoverEntropyInfUni_le_CoverEntropyInf T F Filter.univ_mem)

theorem nonneg_CoverEntropySup_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ CoverEntropySup T F :=
  le_trans (nonneg_CoverEntropyInf_of_nonempty T h) (CoverEntropyInf_le_CoverEntropySup T F)

theorem CoverEntropyInf_eq_CoverEntropySup_of_inv (T : X → X) {F : Set X} (h : MapsTo T F F) :
    CoverEntropyInf T F = CoverEntropySup T F := by
  refine le_antisymm (CoverEntropyInf_le_CoverEntropySup T F) (iSup₂_le (fun U U_uni ↦ ?_))
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  exact le_trans (CoverEntropySupUni_antitone_uni T F V_U)
    <| le_iSup₂_of_le V V_uni (CoverEntropySupUni_le_CoverEntropyInfUni h V_symm)

end DynamicalCover

#lint
