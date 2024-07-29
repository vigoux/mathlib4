/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Order.Filter.Bases
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Group and ring filter bases

A `GroupFilterBasis` is a `FilterBasis` on a group with some properties relating
the basis to the group structure. The main theorem is that a `GroupFilterBasis`
on a group gives a topology on the group which makes it into a topological group
with neighborhoods of the neutral element generated by the given basis.

## Main definitions and results

Given a group `G` and a ring `R`:

* `GroupFilterBasis G`: the type of filter bases that will become neighborhood of `1`
  for a topology on `G` compatible with the group structure
* `GroupFilterBasis.topology`: the associated topology
* `GroupFilterBasis.isTopologicalGroup`: the compatibility between the above topology
  and the group structure
* `RingFilterBasis R`: the type of filter bases that will become neighborhood of `0`
  for a topology on `R` compatible with the ring structure
* `RingFilterBasis.topology`: the associated topology
* `RingFilterBasis.isTopologicalRing`: the compatibility between the above topology
  and the ring structure

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
-/


open Filter Set TopologicalSpace Function

open Topology Filter Pointwise

universe u

/-- A `GroupFilterBasis` on a group is a `FilterBasis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `GroupFilterBasis`. Conversely given a `GroupFilterBasis` one can define a topology
  compatible with the group structure on `G`. -/
class GroupFilterBasis (G : Type u) [Group G] extends FilterBasis G where
  one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U
  mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U
  inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U
  conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ * x * x₀⁻¹) ⁻¹' U

/-- An `AddGroupFilterBasis` on an additive group is a `FilterBasis` satisfying some additional
  axioms. Example : if `G` is a topological group then the neighbourhoods of the identity are an
  `AddGroupFilterBasis`. Conversely given an `AddGroupFilterBasis` one can define a topology
  compatible with the group structure on `G`. -/
class AddGroupFilterBasis (A : Type u) [AddGroup A] extends FilterBasis A where
  zero' : ∀ {U}, U ∈ sets → (0 : A) ∈ U
  add' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U
  neg' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ -x) ⁻¹' U
  conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ + x + -x₀) ⁻¹' U

attribute [to_additive existing] GroupFilterBasis GroupFilterBasis.conj'
  GroupFilterBasis.toFilterBasis

/-- `GroupFilterBasis` constructor in the commutative group case. -/
@[to_additive "`AddGroupFilterBasis` constructor in the additive commutative group case."]
def groupFilterBasisOfComm {G : Type*} [CommGroup G] (sets : Set (Set G))
    (nonempty : sets.Nonempty) (inter_sets : ∀ x y, x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
    (one : ∀ U ∈ sets, (1 : G) ∈ U) (mul : ∀ U ∈ sets, ∃ V ∈ sets, V * V ⊆ U)
    (inv : ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U) : GroupFilterBasis G :=
  { sets := sets
    nonempty := nonempty
    inter_sets := inter_sets _ _
    one' := one _
    mul' := mul _
    inv' := inv _
    conj' := fun x U U_in ↦ ⟨U, U_in, by simp only [mul_inv_cancel_comm, preimage_id']; rfl⟩ }

namespace GroupFilterBasis

variable {G : Type u} [Group G] {B : GroupFilterBasis G}

@[to_additive]
instance : Membership (Set G) (GroupFilterBasis G) :=
  ⟨fun s f ↦ s ∈ f.sets⟩

@[to_additive]
theorem one {U : Set G} : U ∈ B → (1 : G) ∈ U :=
  GroupFilterBasis.one'

@[to_additive]
theorem mul {U : Set G} : U ∈ B → ∃ V ∈ B, V * V ⊆ U :=
  GroupFilterBasis.mul'

@[to_additive]
theorem inv {U : Set G} : U ∈ B → ∃ V ∈ B, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U :=
  GroupFilterBasis.inv'

@[to_additive]
theorem conj : ∀ x₀, ∀ {U}, U ∈ B → ∃ V ∈ B, V ⊆ (fun x ↦ x₀ * x * x₀⁻¹) ⁻¹' U :=
  GroupFilterBasis.conj'

/-- The trivial group filter basis consists of `{1}` only. The associated topology
is discrete. -/
@[to_additive "The trivial additive group filter basis consists of `{0}` only. The associated
topology is discrete."]
instance : Inhabited (GroupFilterBasis G) where
  default := {
    sets := {{1}}
    nonempty := singleton_nonempty _
    inter_sets := by simp
    one' := by simp
    mul' := by simp
    inv' := by simp
    conj' := by simp }

@[to_additive]
theorem subset_mul_self (B : GroupFilterBasis G) {U : Set G} (h : U ∈ B) : U ⊆ U * U :=
  fun x x_in ↦ ⟨1, one h, x, x_in, one_mul x⟩

/-- The neighborhood function of a `GroupFilterBasis`. -/
@[to_additive "The neighborhood function of an `AddGroupFilterBasis`."]
def N (B : GroupFilterBasis G) : G → Filter G :=
  fun x ↦ map (fun y ↦ x * y) B.toFilterBasis.filter

@[to_additive (attr := simp)]
theorem N_one (B : GroupFilterBasis G) : B.N 1 = B.toFilterBasis.filter := by
  simp only [N, one_mul, map_id']

@[to_additive]
protected theorem hasBasis (B : GroupFilterBasis G) (x : G) :
    HasBasis (B.N x) (fun V : Set G ↦ V ∈ B) fun V ↦ (fun y ↦ x * y) '' V :=
  HasBasis.map (fun y ↦ x * y) toFilterBasis.hasBasis

/-- The topological space structure coming from a group filter basis. -/
@[to_additive "The topological space structure coming from an additive group filter basis."]
def topology (B : GroupFilterBasis G) : TopologicalSpace G :=
  TopologicalSpace.mkOfNhds B.N

@[to_additive]
theorem nhds_eq (B : GroupFilterBasis G) {x₀ : G} : @nhds G B.topology x₀ = B.N x₀ := by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun x ↦ (FilterBasis.hasBasis _).map _)
  · intro a U U_in
    exact ⟨1, B.one U_in, mul_one a⟩
  · intro a U U_in
    rcases GroupFilterBasis.mul U_in with ⟨V, V_in, hVU⟩
    filter_upwards [image_mem_map (B.mem_filter_of_mem V_in)]
    rintro _ ⟨x, hx, rfl⟩
    calc
      a • U ⊇ a • (V * V) := smul_set_mono hVU
      _ ⊇ a • x • V := smul_set_mono <| smul_set_subset_smul hx
      _ = (a * x) • V := smul_smul ..
      _ ∈ (a * x) • B.filter := smul_set_mem_smul_filter <| B.mem_filter_of_mem V_in

@[to_additive]
theorem nhds_one_eq (B : GroupFilterBasis G) :
    @nhds G B.topology (1 : G) = B.toFilterBasis.filter := by
  rw [B.nhds_eq]
  simp only [N, one_mul]
  exact map_id

@[to_additive]
theorem nhds_hasBasis (B : GroupFilterBasis G) (x₀ : G) :
    HasBasis (@nhds G B.topology x₀) (fun V : Set G ↦ V ∈ B) fun V ↦ (fun y ↦ x₀ * y) '' V := by
  rw [B.nhds_eq]
  apply B.hasBasis

@[to_additive]
theorem nhds_one_hasBasis (B : GroupFilterBasis G) :
    HasBasis (@nhds G B.topology 1) (fun V : Set G ↦ V ∈ B) id := by
  rw [B.nhds_one_eq]
  exact B.toFilterBasis.hasBasis

@[to_additive]
theorem mem_nhds_one (B : GroupFilterBasis G) {U : Set G} (hU : U ∈ B) :
    U ∈ @nhds G B.topology 1 := by
  rw [B.nhds_one_hasBasis.mem_iff]
  exact ⟨U, hU, rfl.subset⟩

-- See note [lower instance priority]
/-- If a group is endowed with a topological structure coming from a group filter basis then it's a
topological group. -/
@[to_additive "If a group is endowed with a topological structure coming from a group filter basis
then it's a topological group."]
instance (priority := 100) isTopologicalGroup (B : GroupFilterBasis G) :
    @TopologicalGroup G B.topology _ := by
  letI := B.topology
  have basis := B.nhds_one_hasBasis
  have basis' := basis.prod basis
  refine TopologicalGroup.of_nhds_one ?_ ?_ ?_ ?_
  · rw [basis'.tendsto_iff basis]
    suffices ∀ U ∈ B, ∃ V W, (V ∈ B ∧ W ∈ B) ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U by simpa
    intro U U_in
    rcases mul U_in with ⟨V, V_in, hV⟩
    refine ⟨V, V, ⟨V_in, V_in⟩, ?_⟩
    intro a b a_in b_in
    exact hV <| mul_mem_mul a_in b_in
  · rw [basis.tendsto_iff basis]
    intro U U_in
    simpa using inv U_in
  · intro x₀
    rw [nhds_eq, nhds_one_eq]
    rfl
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U U_in
    exact conj x₀ U_in

end GroupFilterBasis

/-- A `RingFilterBasis` on a ring is a `FilterBasis` satisfying some additional axioms.
  Example : if `R` is a topological ring then the neighbourhoods of the identity are a
  `RingFilterBasis`. Conversely given a `RingFilterBasis` on a ring `R`, one can define a
  topology on `R` which is compatible with the ring structure. -/
class RingFilterBasis (R : Type u) [Ring R] extends AddGroupFilterBasis R where
  mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U
  mul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ * x) ⁻¹' U
  mul_right' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x * x₀) ⁻¹' U

namespace RingFilterBasis

variable {R : Type u} [Ring R] (B : RingFilterBasis R)

instance : Membership (Set R) (RingFilterBasis R) :=
  ⟨fun s B ↦ s ∈ B.sets⟩

theorem mul {U : Set R} (hU : U ∈ B) : ∃ V ∈ B, V * V ⊆ U :=
  mul' hU

theorem mul_left (x₀ : R) {U : Set R} (hU : U ∈ B) : ∃ V ∈ B, V ⊆ (fun x ↦ x₀ * x) ⁻¹' U :=
  mul_left' x₀ hU

theorem mul_right (x₀ : R) {U : Set R} (hU : U ∈ B) : ∃ V ∈ B, V ⊆ (fun x ↦ x * x₀) ⁻¹' U :=
  mul_right' x₀ hU

/-- The topology associated to a ring filter basis.
It has the given basis as a basis of neighborhoods of zero. -/
def topology : TopologicalSpace R :=
  B.toAddGroupFilterBasis.topology

/-- If a ring is endowed with a topological structure coming from
a ring filter basis then it's a topological ring. -/
instance (priority := 100) isTopologicalRing {R : Type u} [Ring R] (B : RingFilterBasis R) :
    @TopologicalRing R B.topology _ := by
  let B' := B.toAddGroupFilterBasis
  letI := B'.topology
  have basis := B'.nhds_zero_hasBasis
  have basis' := basis.prod basis
  haveI := B'.isTopologicalAddGroup
  apply TopologicalRing.of_addGroup_of_nhds_zero
  · rw [basis'.tendsto_iff basis]
    suffices ∀ U ∈ B', ∃ V W, (V ∈ B' ∧ W ∈ B') ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U by simpa
    intro U U_in
    rcases B.mul U_in with ⟨V, V_in, hV⟩
    refine ⟨V, V, ⟨V_in, V_in⟩, ?_⟩
    intro a b a_in b_in
    exact hV <| mul_mem_mul a_in b_in
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U
    simpa using B.mul_left x₀
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U
    simpa using B.mul_right x₀

end RingFilterBasis

/-- A `ModuleFilterBasis` on a module is a `FilterBasis` satisfying some additional axioms.
  Example : if `M` is a topological module then the neighbourhoods of zero are a
  `ModuleFilterBasis`. Conversely given a `ModuleFilterBasis` one can define a topology
  compatible with the module structure on `M`. -/
structure ModuleFilterBasis (R M : Type*) [CommRing R] [TopologicalSpace R] [AddCommGroup M]
  [Module R M] extends AddGroupFilterBasis M where
  smul' : ∀ {U}, U ∈ sets → ∃ V ∈ 𝓝 (0 : R), ∃ W ∈ sets, V • W ⊆ U
  smul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ • x) ⁻¹' U
  smul_right' : ∀ (m₀ : M) {U}, U ∈ sets → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ U

namespace ModuleFilterBasis

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  (B : ModuleFilterBasis R M)

instance GroupFilterBasis.hasMem : Membership (Set M) (ModuleFilterBasis R M) :=
  ⟨fun s B ↦ s ∈ B.sets⟩

theorem smul {U : Set M} (hU : U ∈ B) : ∃ V ∈ 𝓝 (0 : R), ∃ W ∈ B, V • W ⊆ U :=
  B.smul' hU

theorem smul_left (x₀ : R) {U : Set M} (hU : U ∈ B) : ∃ V ∈ B, V ⊆ (fun x ↦ x₀ • x) ⁻¹' U :=
  B.smul_left' x₀ hU

theorem smul_right (m₀ : M) {U : Set M} (hU : U ∈ B) : ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ U :=
  B.smul_right' m₀ hU

/-- If `R` is discrete then the trivial additive group filter basis on any `R`-module is a
module filter basis. -/
instance [DiscreteTopology R] : Inhabited (ModuleFilterBasis R M) :=
  ⟨{
      show AddGroupFilterBasis M from
        default with
      smul' := by
        rintro U (rfl : U ∈ {{(0 : M)}})
        use univ, univ_mem, {0}, rfl
        rintro a ⟨x, -, m, rfl, rfl⟩
        simp only [smul_zero, mem_singleton_iff]
      smul_left' := by
        rintro x₀ U (h : U ∈ {{(0 : M)}})
        rw [mem_singleton_iff] at h
        use {0}, rfl
        simp [h]
      smul_right' := by
        rintro m₀ U (h : U ∈ (0 : Set (Set M)))
        rw [Set.mem_zero] at h
        simp [h, nhds_discrete] }⟩

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. -/
def topology : TopologicalSpace M :=
  B.toAddGroupFilterBasis.topology

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. This version gets the ring
topology by unification instead of type class inference. -/
def topology' {R M : Type*} [CommRing R] {_ : TopologicalSpace R} [AddCommGroup M] [Module R M]
    (B : ModuleFilterBasis R M) : TopologicalSpace M :=
  B.toAddGroupFilterBasis.topology

/-- A topological add group with a basis of `𝓝 0` satisfying the axioms of `ModuleFilterBasis`
is a topological module.

This lemma is mathematically useless because one could obtain such a result by applying
`ModuleFilterBasis.continuousSMul` and use the fact that group topologies are characterized
by their neighborhoods of 0 to obtain the `ContinuousSMul` on the pre-existing topology.

But it turns out it's just easier to get it as a byproduct of the proof, so this is just a free
quality-of-life improvement. -/
theorem _root_.ContinuousSMul.of_basis_zero {ι : Type*} [TopologicalRing R] [TopologicalSpace M]
    [TopologicalAddGroup M] {p : ι → Prop} {b : ι → Set M} (h : HasBasis (𝓝 0) p b)
    (hsmul : ∀ {i}, p i → ∃ V ∈ 𝓝 (0 : R), ∃ j, p j ∧ V • b j ⊆ b i)
    (hsmul_left : ∀ (x₀ : R) {i}, p i → ∃ j, p j ∧ MapsTo (x₀ • ·) (b j) (b i))
    (hsmul_right : ∀ (m₀ : M) {i}, p i → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ b i) : ContinuousSMul R M := by
  apply ContinuousSMul.of_nhds_zero
  · rw [h.tendsto_right_iff]
    intro i hi
    rcases hsmul hi with ⟨V, V_in, j, hj, hVj⟩
    apply mem_of_superset (prod_mem_prod V_in <| h.mem_of_mem hj)
    rintro ⟨v, w⟩ ⟨v_in : v ∈ V, w_in : w ∈ b j⟩
    exact hVj (Set.smul_mem_smul v_in w_in)
  · intro m₀
    rw [h.tendsto_right_iff]
    intro i hi
    exact hsmul_right m₀ hi
  · intro x₀
    rw [h.tendsto_right_iff]
    intro i hi
    rcases hsmul_left x₀ hi with ⟨j, hj, hji⟩
    exact mem_of_superset (h.mem_of_mem hj) hji

/-- If a module is endowed with a topological structure coming from
a module filter basis then it's a topological module. -/
instance (priority := 100) continuousSMul [TopologicalRing R] :
    @ContinuousSMul R M _ _ B.topology := by
  let B' := B.toAddGroupFilterBasis
  let _ := B'.topology
  have _ := B'.isTopologicalAddGroup
  exact ContinuousSMul.of_basis_zero B'.nhds_zero_hasBasis
      (fun {_} => by simpa using B.smul)
      (by simpa using B.smul_left) B.smul_right

/-- Build a module filter basis from compatible ring and additive group filter bases. -/
def ofBases {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (BR : RingFilterBasis R)
    (BM : AddGroupFilterBasis M) (smul : ∀ {U}, U ∈ BM → ∃ V ∈ BR, ∃ W ∈ BM, V • W ⊆ U)
    (smul_left : ∀ (x₀ : R) {U}, U ∈ BM → ∃ V ∈ BM, V ⊆ (fun x ↦ x₀ • x) ⁻¹' U)
    (smul_right : ∀ (m₀ : M) {U}, U ∈ BM → ∃ V ∈ BR, V ⊆ (fun x ↦ x • m₀) ⁻¹' U) :
    @ModuleFilterBasis R M _ BR.topology _ _ :=
  let _ := BR.topology
  { BM with
    smul' := by
      intro U U_in
      rcases smul U_in with ⟨V, V_in, W, W_in, H⟩
      exact ⟨V, BR.toAddGroupFilterBasis.mem_nhds_zero V_in, W, W_in, H⟩
    smul_left' := smul_left
    smul_right' := by
      intro m₀ U U_in
      rcases smul_right m₀ U_in with ⟨V, V_in, H⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) H }

end ModuleFilterBasis
