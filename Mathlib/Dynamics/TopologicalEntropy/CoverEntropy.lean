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
is canonical, so the topological entropy depends only on the topological structure. This gives
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset of the whole space. Usually,
one defined the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. However, it is quite painful to work with subtypes and transport
all the necessary information (e.g. a nice description of the topology) to them. The current
version gives a meaning to the topological entropy of a subsystem, and a single lemma
(theorem `subset_restriction_entropy` in `.Systems.Morphism`) will give the equivalence between
both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent)
and to keep the possibility for the entropy to be infinite. Hence, the entropy takes values
in the extended reals `[-∞, +∞]`. The consequence is that we use many somewhat unusual
structures : `ENat`, `ENNReal`, `EReal`. The libraries of `ENat` and `EReal` are quite poor,
which in the case of `EReal` is quite annoying and explain the many additional files. In
addition, the handling of coercions can be quite bothersome, although never as much as with
Lean3.

Finally, I decided to work with minimal hypotheses. In particular, I did not implement a
"topological dynamical system" structure, but tried to keep the hypotheses as sharp as possible
at each point. I thus needed to handle many special cases, but some results are surprisingly
general.

TODO: Check the vocabulary. I introduced `IsDynamicalCoverOf`, `Mincard`, `CoverEntropy`/
`CoverEntropy'` (depending on whether one uses a `liminf` or a `limsup`), `Entropy`/`Entropy'`.
I am not convinced these are the right choices. For instance, I've already encountered `Minspan`
instead of `Mincard`. More importantly, having only `Entropy` as the final object
is somewhat too short: it does not differentiate between the cover or net versions,
which makes some statements ambiguous (and requires some care in the opening/closing
of namespaces).

TODO: The most painful part of the manipulation of topological entropy is going from `Mincard` to
`CoverEntropy`/`CoverEntropy'`: it involves a logarithm, a division, a `liminf`/`limsup`, and
multiple coercions. It is not helped by the weakness of the libraries on `liminf`/`limsup`.
I have not managed to write sensible proofs. Some clean-up would be welcome, although I think that
the best thing to do would be to write a file on "exponential growth" to make a clean passage
from estimates on `Mincard` to estimates on `CoverEntropy`/`CoverEntropy'`.
-/

namespace DynamicalCover

open DynamicalUniformity Uniformity UniformSpace

variable {X : Type*}

/-- A subset F is T-invariant if, for any x ∈ F, T(x) ∈ F. Written with preimages. -/
def IsInvariant (T : X → X) (F : Set X) : Prop := F ⊆ T ⁻¹' F

theorem iter_of_inv_in_inv {T : X → X} {F : Set X} (F_inv : IsInvariant T F) (n : ℕ) :
    F ⊆ T^[n] ⁻¹' F := by
  induction' n with n hn
  . rw [Function.iterate_zero T, Set.preimage_id]
  . rw [Function.iterate_succ T _, Set.preimage_comp]
    exact Set.Subset.trans F_inv (Set.preimage_mono hn)

theorem iter_of_inv_in_inv_apply {T : X → X} {F : Set X} (h : IsInvariant T F) (n : ℕ) {x : X}
    (h' : x ∈ F) :
    T^[n] x ∈ F :=
  (iter_of_inv_in_inv h n) h'

open ENNReal EReal

theorem Ereal_natCast_ne_bot (n : ℕ) : (n : EReal) ≠ ⊥ := Ne.symm (ne_of_beq_false rfl)

theorem Ereal_natCast_ne_top (n : ℕ) : (n : EReal) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)

theorem Ereal_natCast_eq_coe_coe (n : ℕ) :
    (n : EReal) = (n : ℝ) := rfl

theorem Ereal_natCast_mul (m n : ℕ) :
    (m * n : ℕ) = (m : EReal) * (n : EReal) := by
  rw [Ereal_natCast_eq_coe_coe, Ereal_natCast_eq_coe_coe, Ereal_natCast_eq_coe_coe, Nat.cast_mul,
    EReal.coe_mul]

theorem Ereal_natCast_div_le (m n : ℕ) :
    (m / n : ℕ) ≤ (m : EReal) / n := by
  rw [Ereal_natCast_eq_coe_coe, Ereal_natCast_eq_coe_coe, Ereal_natCast_eq_coe_coe, ← EReal.coe_div,
    EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

theorem Ereal_natCast_le (m n : ℕ) : (m : EReal) ≤ n ↔ m ≤ n := by
  rw [Ereal_natCast_eq_coe_coe n, Ereal_natCast_eq_coe_coe m, EReal.coe_le_coe_iff, Nat.cast_le]

theorem ENat.toENNReal_pow (x : ℕ∞) (n : ℕ) : (x ^ n : ℕ∞) = (x : ℝ≥0∞) ^ n := by
  induction n with | zero => simp | succ n hn =>
  rw [pow_succ x n, pow_succ (x : ℝ≥0∞) n, ENat.toENNReal_mul (x ^n) x, hn]

/-!
### Dynamical covers
-/

/-- Given a subset `F`, a uniform neighborhood `U` and an integer `n`, a subset `s` is a `(U, n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an orbit of length `n`
of a point in `s`.-/
def IsDynamicalCoverOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  F ⊆ ⋃ x ∈ s, ball x (DynamicalUni T U n)

theorem dyncover_monotone_time {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ}
    (m_n : m ≤ n) {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F U m s := by
    exact Set.Subset.trans (c := ⋃ x ∈ s, ball x (DynamicalUni T U m)) h
      (Set.iUnion₂_mono fun x _ ↦ ball_mono (dynamical_uni_antitone_time T U m_n) x)

theorem dyncover_antitone_uni {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F V n s := by
  exact Set.Subset.trans (c := ⋃ x ∈ s, ball x (DynamicalUni T V n)) h
    (Set.iUnion₂_mono fun x _ ↦ ball_mono (dynamical_uni_monotone_uni T n U_V) x)

theorem empty_dyncover_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    IsDynamicalCoverOf T ∅ U n ∅ := by
  simp only [IsDynamicalCoverOf, Set.empty_subset]

theorem nonempty_dyncover_of_nonempty {T : X → X} {F : Set X} (h : F.Nonempty) {U : Set (X × X)}
    {n : ℕ} {s : Set X} (h' : IsDynamicalCoverOf T F U n s) :
    s.Nonempty := by
  rcases Set.nonempty_biUnion.1 (Set.Nonempty.mono h' h) with ⟨x, x_s, _⟩
  exact Set.nonempty_of_mem x_s

theorem dyncover_time_zero (T : X → X) (F : Set X) (U : Set (X × X)) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F U 0 s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, not_lt_zero', Prod.map_iterate,
    Set.iInter_of_empty, Set.iInter_univ, Set.preimage_univ]
  rcases h with ⟨x, x_s⟩
  exact Set.subset_iUnion₂_of_subset x x_s (Set.subset_univ F)

theorem dyncover_by_univ (T : X → X) (F : Set X) (n : ℕ) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F Set.univ n s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, Prod.map_iterate, Set.preimage_univ,
    Set.iInter_univ, Set.iUnion_coe_set]
  rcases h with ⟨x, x_s⟩
  exact Set.subset_iUnion₂_of_subset x x_s (Set.subset_univ F)

theorem dyncover_iterate {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (n : ℕ) {s : Finset X} (h : IsDynamicalCoverOf T F V m s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F (V ○ V) (m * n) t ∧ t.card ≤ s.card ^ n := by
  classical
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · use ∅; simp [empty_dyncover_of_empty]
  have _ : Nonempty X := nonempty_of_exists F_nemp
  have s_nemp := nonempty_dyncover_of_nonempty F_nemp h
  rcases F_nemp with ⟨x, x_F⟩
  rcases m.eq_zero_or_pos with (rfl | m_pos)
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact And.intro (dyncover_time_zero T F (V ○ V) (Set.singleton_nonempty x))
      <| one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n
  have :
    ∀ β : Fin n → s, ∃ y : X,
      (⋂ k : Fin n, T^[m * k] ⁻¹' ball (β k) (DynamicalUni T V m)) ⊆
      ball y (DynamicalUni T (V ○ V) (m * n)) := by
    intro t
    rcases Set.eq_empty_or_nonempty (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (DynamicalUni T V m))
      with (inter_empt | inter_nemp)
    · rw [inter_empt]
      use x
      exact Set.empty_subset _
    · rcases inter_nemp with ⟨y, y_int⟩
      use y
      intro z z_int
      simp only [ball, DynamicalUni, Prod.map_iterate, Set.mem_preimage, Set.mem_iInter,
        Prod.map_apply] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball V_symm y_int z_int
  choose! dyncover h_dyncover using this
  let sn := Set.range dyncover
  have _ := Set.fintypeRange dyncover
  use sn.toFinset
  constructor
  · rw [Finset.coe_nonempty] at s_nemp
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nemp
    intro y y_F
    have key : ∀ k : Fin n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (DynamicalUni T V m) := by
      intro k
      have := h (iter_of_inv_in_inv_apply F_inv (m * k) y_F)
      simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at this
      rcases this with ⟨z, z_s, hz⟩
      use ⟨z, z_s⟩
      exact hz
    choose! t ht using key
    specialize h_dyncover t
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, Set.toFinset_range,
      Finset.mem_image, Finset.mem_univ, true_and, exists_prop, exists_exists_eq_and, sn]
    simp only [Set.mem_preimage, Subtype.forall, Finset.mem_range] at ht
    use dyncover t
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      exists_apply_eq_apply, true_and]
    apply h_dyncover
    simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
    exact ht
  · rw [Set.toFinset_card]
    apply le_trans (Fintype.card_range_le dyncover)
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

/-theorem dyncover_iterate' {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (m_pos : 0 < m) (n : ℕ) {s : Finset X}
    (h : IsDynamicalCoverOf T F V m s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F (compRel V V) n t ∧ t.card ≤ s.card ^ (n / m + 1) := by
  cases' dyncover_iterate F_inv V_symm (n / m + 1) h with t ht
  use t
  exact ⟨dyncover_monotone_time (le_of_lt (Nat.lt_mul_div_succ n m_pos)) ht.1, ht.2⟩-/

theorem exists_dyncover_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) (F_comp : IsCompact F) {U : Set (X × X)} (hU : U ∈ 𝓤 X)
    (n : ℕ) :
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s := by
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, V_uni, V_symm, V_U⟩
  let open_cover := fun x : X ↦ ball x V
  have := IsCompact.elim_nhds_subcover F_comp open_cover (fun (x : X) _ ↦ ball_mem_nhds x V_uni)
  rcases this with ⟨s, _, s_cover⟩
  have : IsDynamicalCoverOf T F V 1 s := by
    intro x x_F
    specialize s_cover x_F
    simp only [Set.mem_iUnion, exists_prop] at s_cover
    rcases s_cover with ⟨y, y_s, _⟩
    simp only [DynamicalUni, Nat.lt_one_iff, Set.iInter_iInter_eq_left, Function.iterate_zero,
      Prod.map_id, Set.preimage_id_eq, id_eq, Set.mem_iUnion]
    use y, y_s
  rcases dyncover_iterate F_inv V_symm n this with ⟨t, t_dyncover, t_card⟩
  rw [one_mul n] at t_dyncover
  use t
  exact dyncover_antitone_uni V_U t_dyncover

/-!
### Minimal cardinal of dynamical covers
-/

/-- The smallest cardinal of a `(U, n)`-dynamical cover of `F`. Takes values in `ℕ∞`, and is infinite
if and only if `F` admits no finite dynamical cover.-/
noncomputable def Mincard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynamicalCoverOf T F U n s), (s.card : ℕ∞)

theorem mincard_eq_sInf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n
    = sInf (WithTop.some '' (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s})) := by
  unfold Mincard
  rw [← Set.image_comp, sInf_image]
  simp only [Set.mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]

theorem mincard_le_card {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    Mincard T F U n ≤ s.card := iInf₂_le s h

theorem finite_mincard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s ∧ s.card = Mincard T F U n := by
  apply Iff.intro _ (fun ⟨s, _, s_mincard⟩ ↦ Eq.symm s_mincard ▸ WithTop.coe_lt_top s.card)
  rw [mincard_eq_sInf T F U n]
  intro mincard_fin
  rcases WithTop.ne_top_iff_exists.1 (ne_of_lt mincard_fin) with ⟨k, k_mincard⟩
  rw [← k_mincard]
  simp only [ENat.some_eq_coe, Nat.cast_inj]
  have h_nemp : Set.Nonempty (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}) := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp only [ENat.some_eq_coe, h, Set.image_empty, sInf_empty, lt_self_iff_false]
      at mincard_fin
  have h_bddb : BddBelow (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}) := by
    use 0
    simp only [lowerBounds, Set.mem_setOf_eq, zero_le, implies_true]
  rw [← WithTop.coe_sInf' h_nemp h_bddb] at k_mincard
  norm_cast at k_mincard
  have := Nat.sInf_mem h_nemp
  rw [← k_mincard] at this
  simp only [Set.mem_image, Set.mem_setOf_eq] at this
  exact this

theorem finite_mincard_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
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
  simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at h
  rcases h with ⟨z, z_s, y_Bz⟩
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
  use z
  exact ⟨⟨z_s, Set.nonempty_of_mem ⟨y_Bz, y_F⟩⟩, y_Bz⟩

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
    simp only [Finset.mem_coe, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨z, z_s, hz⟩
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff,
      Set.mem_iUnion, exists_prop, t]
    use z
    refine And.intro (And.intro z_s fun z_x ↦ ?_) hz
    rw [z_x] at hz
    apply Set.not_mem_empty y
    rw [← ball_empt]
    exact Set.mem_inter y_F hz
  apply not_lt_of_le (mincard_le_card t_smaller_cover)
  rw [← h']
  norm_cast
  exact Finset.card_erase_lt_of_mem x_s

theorem mincard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ Mincard T F U n) := by
  intros m n m_n
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F U m]
  apply sInf_le_sInf
  apply Set.image_subset
  apply Set.image_subset
  exact fun s ↦ dyncover_monotone_time m_n

theorem mincard_antitone_uni (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X×X) ↦ Mincard T F U n) := by
  intros U V U_V
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F V n]
  apply sInf_le_sInf
  apply Set.image_subset
  apply Set.image_subset
  exact fun s ↦ dyncover_antitone_uni U_V

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
    Finset.card_eq_zero, exists_eq_right, Finset.not_mem_empty, Set.iUnion_of_empty,
    Set.iUnion_empty, true_iff] at this
  exact Set.eq_empty_iff_forall_not_mem.2 this

theorem nonempty_iff_mincard_pos (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F.Nonempty ↔ 1 ≤ Mincard T F U n := by
  rw [ENat.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty, not_iff_not]
  exact empty_iff_mincard_zero T F U n

theorem mincard_time_zero_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty)
    (U : Set (X × X)) :
    Mincard T F U 0 = 1 := by
  apply le_antisymm _ ((nonempty_iff_mincard_pos T F U 0).1 h)
  rcases h with ⟨x, _⟩
  have := (dyncover_time_zero T F U (Set.singleton_nonempty x))
  rw [← Finset.coe_singleton] at this
  apply le_of_le_of_eq (mincard_le_card this)
  rw [Finset.card_singleton, Nat.cast_one]

theorem mincard_time_zero_le (T : X → X) (F : Set X) (U : Set (X × X)) :
    Mincard T F U 0 ≤ 1 := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · exact mincard_of_empty ▸ zero_le_one
  · rw [mincard_time_zero_of_nonempty T F_nemp U]

theorem mincard_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    Mincard T F Set.univ n = 1 := by
  apply le_antisymm _ ((nonempty_iff_mincard_pos T F Set.univ n).1 h)
  rcases h with ⟨x, _⟩
  have := (dyncover_by_univ T F n (Set.singleton_nonempty x))
  rw [← Finset.coe_singleton] at this
  apply le_of_le_of_eq (mincard_le_card this)
  rw [Finset.card_singleton, Nat.cast_one]

theorem mincard_by_univ_le (T : X → X) (F : Set X) (n : ℕ) :
    Mincard T F Set.univ n ≤ 1 := by
  rcases F.eq_empty_or_nonempty with (rfl | h)
  · exact mincard_of_empty ▸ zero_le_one
  · rw [mincard_by_univ_of_nonempty T h n]

theorem mincard_iterate {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) (m n : ℕ) :
    Mincard T F (V ○ V) (m * n) ≤ Mincard T F V m ^ n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · rw [mincard_of_empty]; exact zero_le _
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [mul_zero, mincard_time_zero_of_nonempty T F_nonempty (V ○ V), pow_zero]
  rcases eq_top_or_lt_top (Mincard T F V m) with (h | h)
  · exact h ▸ le_of_le_of_eq (le_top (α := ℕ∞)) (Eq.symm (ENat.top_pow n_pos))
  · rcases (finite_mincard_iff T F V m).1 h with ⟨s, s_cover, s_mincard⟩
    rcases dyncover_iterate F_inv V_symm n s_cover with ⟨t, t_cover, t_le_sn⟩
    rw [← s_mincard]
    exact le_trans (mincard_le_card t_cover) (WithTop.coe_le_coe.2 t_le_sn)

theorem mincard_upper_bound {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    Mincard T F (V ○ V) n ≤ Mincard T F V m ^ (n / m + 1) :=
  le_trans (mincard_monotone_time T F (V ○ V) (le_of_lt (Nat.lt_mul_div_succ n m_pos)))
    (mincard_iterate F_inv V_symm m (n / m + 1))

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

theorem log_mincard_iterate {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) (m : ℕ) {n : ℕ} (n_pos : 0 < n) :
    log (Mincard T F (V ○ V) (m * n)) / n ≤ log (Mincard T F V m) := by
  apply (EReal.div_le_iff_le_mul (b := n) (Nat.cast_pos'.2 n_pos) (Ereal_natCast_ne_top n)).2
  rw [← log_pow, StrictMono.le_iff_le log_strictMono]
  nth_rw 2 [← ENat.toENNRealRingHom_apply]
  rw [← RingHom.map_pow ENat.toENNRealRingHom _ n, ENat.toENNRealRingHom_apply, ENat.toENNReal_le]
  exact mincard_iterate F_inv V_symm m n

theorem log_mincard_upper_bound {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) {m n : ℕ} (m_pos : 0 < m) (n_pos : 0 < n) :
    log (Mincard T F (V ○ V) n) / n ≤ log (Mincard T F V m) / m + log (Mincard T F V m) / n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · rw [mincard_of_empty, ENat.toENNReal_zero, log_zero,
      bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (Ereal_natCast_ne_top n)]
    exact bot_le
  have h_nm : (0 : EReal) ≤ (n / m : ℕ) := Nat.cast_nonneg' (n / m)
  have h_log := log_mincard_nonneg_of_nonempty T F_nemp V m
  have n_div_n := EReal.div_self (Ereal_natCast_ne_bot n) (Ereal_natCast_ne_top n)
    (ne_of_gt (Nat.cast_pos'.2 n_pos))
  apply le_trans <| div_le_div_right_of_nonneg (le_of_lt (Nat.cast_pos'.2 n_pos))
    (log_monotone (ENat.toENNReal_le.2 (mincard_upper_bound F_inv V_symm m_pos n)))
  rw [ENat.toENNReal_pow, log_pow, Nat.cast_add, Nat.cast_one, right_distrib_of_nonneg h_nm
    zero_le_one, one_mul, div_right_distrib_of_nonneg (Left.mul_nonneg h_nm h_log) h_log, mul_comm,
    ← EReal.mul_div, div_eq_mul_inv _ (m : EReal)]
  apply add_le_add_right (mul_le_mul_of_nonneg_left _ h_log)
  apply le_of_le_of_eq <| div_le_div_right_of_nonneg (le_of_lt (Nat.cast_pos'.2 n_pos))
    (Ereal_natCast_div_le n m)
  rw [EReal.div_div, mul_comm, ← EReal.div_div, n_div_n, one_div (m : EReal)]

/-!
### Cover entropy of uniformities
-/

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
    exact fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (Ereal_natCast_ne_top n)

@[simp]
theorem CoverEntropyInfUni_of_empty {T : X → X} {U : Set (X × X)} :
    CoverEntropyInfUni T ∅ U = ⊥ :=
  le_bot_iff.1 <| le_of_le_of_eq
    (CoverEntropyInfUni_le_CoverEntropySupUni T ∅ U) CoverEntropySupUni_of_empty

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
    CoverEntropyInfUni T F Set.univ = 0 := by
  simp [CoverEntropyInfUni, mincard_by_univ_of_nonempty T h]

theorem CoverEntropySupUni_by_univ_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    CoverEntropySupUni T F Set.univ = 0 := by
  simp [CoverEntropySupUni, mincard_by_univ_of_nonempty T h]

theorem CoverEntropyInfUni_le_log_mincard_div {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropyInfUni T F (V ○ V) ≤ log (Mincard T F V n) / n := by
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
  · have := log_mincard_iterate F_inv V_symm n (lt_of_lt_of_le zero_lt_one (le_max_left 1 N))
    rw [mul_comm n (max 1 N)] at this
    apply le_of_eq_of_le _ (div_le_div_right_of_nonneg (Nat.cast_nonneg' n) this)
    rw [EReal.div_div]
    congr
    exact Ereal_natCast_mul (max 1 N) n

theorem CoverEntropyInfUni_le_card_div {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) {s : Finset X}
    (h : IsDynamicalCoverOf T F V n s) :
    CoverEntropyInfUni T F (V ○ V) ≤ log s.card / n := by
  apply le_trans (CoverEntropyInfUni_le_log_mincard_div F_inv V_symm n_pos)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  apply log_monotone
  norm_cast
  exact mincard_le_card h

/-lemma intermediate_lemma (a : EReal) (m : ℕ) :
    Filter.Tendsto (fun (n : ℕ) ↦ a * (m / n + 1 : ENNReal)) Filter.atTop (nhds a) := by
  have : (fun (n : ℕ) ↦ a * (m / n + 1 : ENNReal))
      = (fun p : EReal × EReal ↦ p.1 * p.2)
      ∘ (fun (n : ℕ) ↦ Prod.mk a ((m / n + 1 : ENNReal) : EReal)) := by
    ext n
    simp
  rw [this]; clear this
  have one_ne_top : (1 : EReal) ≠ ⊤ := by decide
  have key := ContinuousAt.tendsto <| @ERealMulCont.continuousAt_mul (a, 1)
    (Or.inr  WithBot.one_ne_bot) (Or.inr one_ne_top) (Or.inr one_ne_zero) (Or.inr one_ne_zero)
  simp only [mul_one] at key
  apply Filter.Tendsto.comp key; clear key one_ne_top
  rw [Prod.tendsto_iff]
  constructor; exact tendsto_const_nhds
  simp only [EReal.coe_ennreal_add, EReal.coe_ennreal_one]; clear a
  have limit_zero := @ENNReal.Tendsto.const_div ℕ Filter.atTop (fun (n : ℕ) ↦ (n : ENNReal))
    m ⊤ ENNReal.tendsto_nat_nhds_top (Or.inr <| ENNReal.natCast_ne_top m)
  simp only [EReal.div_top] at limit_zero
  have limit_one : Filter.Tendsto (fun (_ : ℕ) ↦ (1 : ENNReal)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have key := Filter.Tendsto.add limit_zero limit_one; clear limit_zero limit_one
  rw [zero_add] at key
  have : (fun (n : ℕ) ↦ ((m / n : ENNReal)+1 : EReal))
      = ENNReal.toEReal ∘ (fun (n : ℕ) ↦ (m / n + 1 : ENNReal)) := by
    ext n
    simp only [Function.comp_apply, EReal.coe_ennreal_add, EReal.coe_ennreal_one]
  rw [this]; clear this
  apply Filter.Tendsto.comp _ key
  exact ContinuousAt.tendsto (Continuous.continuousAt continuous_coe_ennreal_ereal)-/

/-theorem cover_entropy'_le_log_mincard_div {X : Type _} {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropy' T F (compRel V V) ≤ log (Mincard T F V n) / (n : ENNReal) := by
  have upper_bound := log_mincard_upper_bound' F_inv V_symm n_pos
  replace upper_bound := @Filter.eventually_of_forall _ _ Filter.atTop upper_bound
  apply le_trans (Misc.EReal_limsup_le_limsup upper_bound); clear upper_bound
  apply le_of_eq
  apply Filter.Tendsto.limsup_eq
  exact intermediate_lemma (log (Mincard T F V n) / (n : ENNReal)) n-/

theorem CoverEntropySupUni_le_log_mincard_div {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropySupUni T F (V ○ V) ≤ log (Mincard T F V n) / n := by
  let u := fun m : ℕ ↦ log (Mincard T F V n) / n
  let v := fun m : ℕ ↦ log (Mincard T F V n) / m
  let w := fun m : ℕ ↦ log (Mincard T F (V ○ V) m) / m
  have key : w ≤ᶠ[Filter.atTop] u + v := by
    apply Filter.eventually_atTop.2
    use 1
    simp only [Pi.add_apply, w, u, v]
    intro m m_pos
    exact log_mincard_upper_bound F_inv V_symm n_pos m_pos
  apply le_trans (limsup_le_limsup key)
  suffices h : Filter.atTop.limsup v = 0
  · have := @limsup_add_le_add_limsup ℕ Filter.atTop u v
    rw [h, add_zero] at this
    specialize this (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)
    exact le_of_le_of_eq this (Filter.limsup_const (log (Mincard T F V n) / n))
  apply Filter.Tendsto.limsup_eq
  simp [v]
  sorry

theorem CoverEntropySupUni_le_CoverEntropyInfUni {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) :
    CoverEntropySupUni T F (V ○ V) ≤ CoverEntropyInfUni T F V := by
  apply (Filter.le_liminf_of_le)
  apply Filter.eventually_atTop.2
  use 1
  exact fun m m_pos ↦ CoverEntropySupUni_le_log_mincard_div F_inv V_symm m_pos

theorem finite_CoverEntropyInfUni_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) (F_comp : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) :
    CoverEntropyInfUni T F U < ⊤ := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  rcases exists_dyncover_of_compact_inv F_inv F_comp V_uni 1 with ⟨s, s_cover⟩
  apply lt_of_le_of_lt (CoverEntropyInfUni_antitone_uni T F V_U)
  apply lt_of_le_of_lt (CoverEntropyInfUni_le_card_div F_inv V_symm zero_lt_one s_cover)
  rw [Nat.cast_one, div_one, log_lt_top_iff, ← ENat.toENNReal_top]
  norm_cast
  exact Ne.lt_top (ENat.coe_ne_top (Finset.card s))

/- Simplify.-/
/- Same for CoverEntropySupUni?-/

/-!
### Cover entropy
-/

/-- The entropy of T restricted to F, obtained by taking the supremum over uniformity neighbourhoods.
Note that this supremum is approached by taking small neighbourhoods.--/
noncomputable def CoverEntropyInf [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, CoverEntropyInfUni T F U

/-- An alternative definition of the entropy of T restricted to F, using a limsup instead of
a liminf.--/
noncomputable def CoverEntropySup [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, CoverEntropySupUni T F U

theorem CoverEntropyInf_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @CoverEntropyInf X u T F := by
  intro u₁ u₂ h
  apply iSup₂_mono'
  intro U U_uni₂
  use U, (Filter.le_def.1 h) U U_uni₂

theorem CoverEntropySup_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @CoverEntropySup X u T F := by
  intro u₁ u₂ h
  apply iSup₂_mono'
  intro U U_uni₂
  use U, (Filter.le_def.1 h) U U_uni₂

variable [UniformSpace X]

theorem CoverEntropyInf_le_CoverEntropySup (T : X → X) (F : Set X) :
    CoverEntropyInf T F ≤ CoverEntropySup T F :=
  iSup₂_mono (fun (U : Set (X × X)) (_ : U ∈ uniformity X)
    ↦ CoverEntropyInfUni_le_CoverEntropySupUni T F U)

theorem CoverEntropyInfUni_le_CoverEntropyInf (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    CoverEntropyInfUni T F U ≤ CoverEntropyInf T F := by apply le_iSup₂ U h

theorem CoverEntropySupUni_le_CoverEntropySup (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    CoverEntropySupUni T F U ≤ CoverEntropySup T F := by apply le_iSup₂ U h

@[simp]
theorem CoverEntropyInf_of_empty {T : X → X} : CoverEntropyInf T ∅ = ⊥ := by
  simp only [CoverEntropyInf, CoverEntropyInfUni_of_empty, iSup_bot]

@[simp]
theorem CoverEntropySup_of_empty {T : X → X} : CoverEntropySup T ∅ = ⊥ := by
  simp only [CoverEntropySup, CoverEntropySupUni_of_empty, iSup_bot]

theorem nonneg_CoverEntropyInf_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ CoverEntropyInf T F := by
  apply le_iSup_of_le Set.univ
  simp only [Filter.univ_mem, iSup_pos]
  exact nonneg_CoverEntropyInfUni_of_nonempty T h Set.univ

theorem nonneg_CoverEntropySup_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ CoverEntropySup T F :=
  le_trans (nonneg_CoverEntropyInf_of_nonempty T h) (CoverEntropyInf_le_CoverEntropySup T F)

/-theorem entropy_eq_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    CoverEntropyInf T F = CoverEntropySup T F := by
  apply le_antisymm (entropy_le_entropy' T F)
  apply iSup₂_le; intros U U_uni
  rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
  apply le_trans (cover_entropy'_antitone_uni T F V_comp_U)
  apply le_iSup₂_of_le V V_uni
  exact cover_entropy'_le h V_symm-/

/- TODO : sup can be taken over a family generating 𝓤 X.-/

end DynamicalCover

#lint
