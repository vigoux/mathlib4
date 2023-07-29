/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Topology.Separation
import Mathlib.Data.Set.Intervals.Monotone

#align_import topology.filter from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Topology on the set of filters on a type

This file introduces a topology on `Filter α`. It is generated by the sets
`Set.Iic (𝓟 s) = {l : Filter α | s ∈ l}`, `s : Set α`. A set `s : Set (Filter α)` is open if and
only if it is a union of a family of these basic open sets, see `Filter.isOpen_iff`.

This topology has the following important properties.

* If `X` is a topological space, then the map `𝓝 : X → Filter X` is a topology inducing map.

* In particular, it is a continuous map, so `𝓝 ∘ f` tends to `𝓝 (𝓝 a)` whenever `f` tends to `𝓝 a`.

* If `X` is an ordered topological space with order topology and no max element, then `𝓝 ∘ f` tends
  to `𝓝 Filter.atTop` whenever `f` tends to `Filter.atTop`.

* It turns `Filter X` into a T₀ space and the order on `Filter X` is the dual of the
  `specializationOrder (Filter X)`.

## Tags

filter, topological space
-/


open Set Filter TopologicalSpace

open Filter Topology

variable {ι : Sort _} {α β X Y : Type _}

namespace Filter

/-- The topology on `Filter α` is generated by the sets `Set.Iic (𝓟 s) = {l : Filter α | s ∈ l}`,
`s : Set α`. A set `s : Set (Filter α)` is open if and only if it is a union of a family of these
basic open sets, see `Filter.isOpen_iff`. -/
instance : TopologicalSpace (Filter α) :=
  generateFrom <| range <| Iic ∘ 𝓟

theorem isOpen_Iic_principal {s : Set α} : IsOpen (Iic (𝓟 s)) :=
  GenerateOpen.basic _ (mem_range_self _)
#align filter.is_open_Iic_principal Filter.isOpen_Iic_principal

theorem isOpen_setOf_mem {s : Set α} : IsOpen { l : Filter α | s ∈ l } := by
  simpa only [Iic_principal] using isOpen_Iic_principal
#align filter.is_open_set_of_mem Filter.isOpen_setOf_mem

theorem isTopologicalBasis_Iic_principal :
    IsTopologicalBasis (range (Iic ∘ 𝓟 : Set α → Set (Filter α))) :=
  { exists_subset_inter := by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ l hl
      exact ⟨Iic (𝓟 s) ∩ Iic (𝓟 t), ⟨s ∩ t, by simp⟩, hl, Subset.rfl⟩
    sUnion_eq := sUnion_eq_univ_iff.2 fun l => ⟨Iic ⊤, ⟨univ, congr_arg Iic principal_univ⟩,
      mem_Iic.2 le_top⟩
    eq_generateFrom := rfl }
#align filter.is_topological_basis_Iic_principal Filter.isTopologicalBasis_Iic_principal

theorem isOpen_iff {s : Set (Filter α)} : IsOpen s ↔ ∃ T : Set (Set α), s = ⋃ t ∈ T, Iic (𝓟 t) :=
  isTopologicalBasis_Iic_principal.open_iff_eq_sUnion.trans <| by
    simp only [exists_subset_range_and_iff, sUnion_image, (· ∘ ·)]
#align filter.is_open_iff Filter.isOpen_iff

theorem nhds_eq (l : Filter α) : 𝓝 l = l.lift' (Iic ∘ 𝓟) :=
  nhds_generateFrom.trans <| by
    simp only [mem_setOf_eq, @and_comm (l ∈ _), iInf_and, iInf_range, Filter.lift', Filter.lift,
      (· ∘ ·), mem_Iic, le_principal_iff]
#align filter.nhds_eq Filter.nhds_eq

theorem nhds_eq' (l : Filter α) : 𝓝 l = l.lift' fun s => { l' | s ∈ l' } := by
  simpa only [(· ∘ ·), Iic_principal] using nhds_eq l
#align filter.nhds_eq' Filter.nhds_eq'

protected theorem tendsto_nhds {la : Filter α} {lb : Filter β} {f : α → Filter β} :
    Tendsto f la (𝓝 lb) ↔ ∀ s ∈ lb, ∀ᶠ a in la, s ∈ f a := by
  simp only [nhds_eq', tendsto_lift', mem_setOf_eq]
#align filter.tendsto_nhds Filter.tendsto_nhds

protected theorem HasBasis.nhds {l : Filter α} {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis (𝓝 l) p fun i => Iic (𝓟 (s i)) := by
  rw [nhds_eq]
  exact h.lift' monotone_principal.Iic
#align filter.has_basis.nhds Filter.HasBasis.nhds

/-- Neighborhoods of a countably generated filter is a countably generated filter. -/
instance {l : Filter α} [IsCountablyGenerated l] : IsCountablyGenerated (𝓝 l) :=
  let ⟨_b, hb⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated <| ⟨hb.nhds, Set.to_countable _⟩

theorem HasBasis.nhds' {l : Filter α} {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis (𝓝 l) p fun i => { l' | s i ∈ l' } := by simpa only [Iic_principal] using h.nhds
#align filter.has_basis.nhds' Filter.HasBasis.nhds'

theorem mem_nhds_iff {l : Filter α} {S : Set (Filter α)} : S ∈ 𝓝 l ↔ ∃ t ∈ l, Iic (𝓟 t) ⊆ S :=
  l.basis_sets.nhds.mem_iff
#align filter.mem_nhds_iff Filter.mem_nhds_iff

theorem mem_nhds_iff' {l : Filter α} {S : Set (Filter α)} :
    S ∈ 𝓝 l ↔ ∃ t ∈ l, ∀ ⦃l' : Filter α⦄, t ∈ l' → l' ∈ S :=
  l.basis_sets.nhds'.mem_iff
#align filter.mem_nhds_iff' Filter.mem_nhds_iff'

@[simp]
theorem nhds_bot : 𝓝 (⊥ : Filter α) = pure ⊥ := by
  simp [nhds_eq, (· ∘ ·), lift'_bot monotone_principal.Iic]
#align filter.nhds_bot Filter.nhds_bot

@[simp]
theorem nhds_top : 𝓝 (⊤ : Filter α) = ⊤ := by simp [nhds_eq]
#align filter.nhds_top Filter.nhds_top

@[simp]
theorem nhds_principal (s : Set α) : 𝓝 (𝓟 s) = 𝓟 (Iic (𝓟 s)) :=
  (hasBasis_principal s).nhds.eq_of_same_basis (hasBasis_principal _)
#align filter.nhds_principal Filter.nhds_principal

@[simp]
theorem nhds_pure (x : α) : 𝓝 (pure x : Filter α) = 𝓟 {⊥, pure x} := by
  rw [← principal_singleton, nhds_principal, principal_singleton, Iic_pure]
#align filter.nhds_pure Filter.nhds_pure

@[simp]
theorem nhds_iInf (f : ι → Filter α) : 𝓝 (⨅ i, f i) = ⨅ i, 𝓝 (f i) := by
  simp only [nhds_eq]
  apply lift'_iInf_of_map_univ <;> simp
#align filter.nhds_infi Filter.nhds_iInf

@[simp]
theorem nhds_inf (l₁ l₂ : Filter α) : 𝓝 (l₁ ⊓ l₂) = 𝓝 l₁ ⊓ 𝓝 l₂ := by
  simpa only [iInf_bool_eq] using nhds_iInf fun b => cond b l₁ l₂
#align filter.nhds_inf Filter.nhds_inf

theorem monotone_nhds : Monotone (𝓝 : Filter α → Filter (Filter α)) :=
  Monotone.of_map_inf nhds_inf
#align filter.monotone_nhds Filter.monotone_nhds

theorem sInter_nhds (l : Filter α) : ⋂₀ { s | s ∈ 𝓝 l } = Iic l := by
  simp_rw [nhds_eq, (· ∘ ·), sInter_lift'_sets monotone_principal.Iic, Iic, le_principal_iff,
    ← setOf_forall, ← Filter.le_def]
#align filter.Inter_nhds Filter.sInter_nhds

@[simp]
theorem nhds_mono {l₁ l₂ : Filter α} : 𝓝 l₁ ≤ 𝓝 l₂ ↔ l₁ ≤ l₂ := by
  refine' ⟨fun h => _, fun h => monotone_nhds h⟩
  rw [← Iic_subset_Iic, ← sInter_nhds, ← sInter_nhds]
  exact sInter_subset_sInter h
#align filter.nhds_mono Filter.nhds_mono

protected theorem mem_interior {s : Set (Filter α)} {l : Filter α} :
    l ∈ interior s ↔ ∃ t ∈ l, Iic (𝓟 t) ⊆ s := by rw [mem_interior_iff_mem_nhds, mem_nhds_iff]
#align filter.mem_interior Filter.mem_interior

protected theorem mem_closure {s : Set (Filter α)} {l : Filter α} :
    l ∈ closure s ↔ ∀ t ∈ l, ∃ l' ∈ s, t ∈ l' := by
  simp only [closure_eq_compl_interior_compl, Filter.mem_interior, mem_compl_iff, not_exists,
    not_forall, Classical.not_not, exists_prop, not_and, and_comm, subset_def, mem_Iic,
    le_principal_iff]
#align filter.mem_closure Filter.mem_closure

@[simp]
protected theorem closure_singleton (l : Filter α) : closure {l} = Ici l := by
  ext l'
  simp [Filter.mem_closure, Filter.le_def]
#align filter.closure_singleton Filter.closure_singleton

@[simp]
theorem specializes_iff_le {l₁ l₂ : Filter α} : l₁ ⤳ l₂ ↔ l₁ ≤ l₂ := by
  simp only [specializes_iff_closure_subset, Filter.closure_singleton, Ici_subset_Ici]
#align filter.specializes_iff_le Filter.specializes_iff_le

instance : T0Space (Filter α) :=
  ⟨fun _ _ h => (specializes_iff_le.1 h.specializes).antisymm
    (specializes_iff_le.1 h.symm.specializes)⟩

theorem nhds_atTop [Preorder α] : 𝓝 atTop = ⨅ x : α, 𝓟 (Iic (𝓟 (Ici x))) := by
  simp only [atTop, nhds_iInf, nhds_principal]
#align filter.nhds_at_top Filter.nhds_atTop

protected theorem tendsto_nhds_atTop_iff [Preorder β] {l : Filter α} {f : α → Filter β} :
    Tendsto f l (𝓝 atTop) ↔ ∀ y, ∀ᶠ a in l, Ici y ∈ f a := by
  simp only [nhds_atTop, tendsto_iInf, tendsto_principal, mem_Iic, le_principal_iff]
#align filter.tendsto_nhds_at_top_iff Filter.tendsto_nhds_atTop_iff

theorem nhds_atBot [Preorder α] : 𝓝 atBot = ⨅ x : α, 𝓟 (Iic (𝓟 (Iic x))) :=
  @nhds_atTop αᵒᵈ _
#align filter.nhds_at_bot Filter.nhds_atBot

protected theorem tendsto_nhds_atBot_iff [Preorder β] {l : Filter α} {f : α → Filter β} :
    Tendsto f l (𝓝 atBot) ↔ ∀ y, ∀ᶠ a in l, Iic y ∈ f a :=
  @Filter.tendsto_nhds_atTop_iff α βᵒᵈ _ _ _
#align filter.tendsto_nhds_at_bot_iff Filter.tendsto_nhds_atBot_iff

variable [TopologicalSpace X]

theorem nhds_nhds (x : X) : 𝓝 (𝓝 x) = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 (Iic (𝓟 s)) :=
  by simp only [(nhds_basis_opens x).nhds.eq_biInf, iInf_and, @iInf_comm _ (_ ∈ _)]
#align filter.nhds_nhds Filter.nhds_nhds

theorem inducing_nhds : Inducing (𝓝 : X → Filter X) :=
  inducing_iff_nhds.2 fun x =>
    (nhds_def' _).trans <| by
      simp (config := { contextual := true }) only [nhds_nhds, comap_iInf, comap_principal,
        Iic_principal, preimage_setOf_eq, ← mem_interior_iff_mem_nhds, setOf_mem_eq,
        IsOpen.interior_eq]
#align filter.inducing_nhds Filter.inducing_nhds

@[continuity]
theorem continuous_nhds : Continuous (𝓝 : X → Filter X) :=
  inducing_nhds.continuous
#align filter.continuous_nhds Filter.continuous_nhds

protected theorem Tendsto.nhds {f : α → X} {l : Filter α} {x : X} (h : Tendsto f l (𝓝 x)) :
    Tendsto (𝓝 ∘ f) l (𝓝 (𝓝 x)) :=
  (continuous_nhds.tendsto _).comp h
#align filter.tendsto.nhds Filter.Tendsto.nhds

end Filter

variable [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {x : X} {s : Set X}

protected nonrec theorem ContinuousWithinAt.nhds (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (𝓝 ∘ f) s x :=
  h.nhds
#align continuous_within_at.nhds ContinuousWithinAt.nhds

protected nonrec theorem ContinuousAt.nhds (h : ContinuousAt f x) : ContinuousAt (𝓝 ∘ f) x :=
  h.nhds
#align continuous_at.nhds ContinuousAt.nhds

protected nonrec theorem ContinuousOn.nhds (h : ContinuousOn f s) : ContinuousOn (𝓝 ∘ f) s :=
  fun x hx => (h x hx).nhds
#align continuous_on.nhds ContinuousOn.nhds

protected nonrec theorem Continuous.nhds (h : Continuous f) : Continuous (𝓝 ∘ f) :=
  Filter.continuous_nhds.comp h
#align continuous.nhds Continuous.nhds
