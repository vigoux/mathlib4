/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Topology.GDelta
import Mathlib.MeasureTheory.Constructions.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

variable (α : Type*) {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

notation:50 f " =ᵇ " g:50 => Filter.EventuallyEq (residual _) f g
notation3 "∀ᵇ "(...)", "r:(scoped p => Filter.Eventually p <| residual _) => r
notation3 "∃ᵇ "(...)", "r:(scoped p => Filter.Frequently p <| residual _) => r

def BaireMeasurableSpace : Type _ := α

variable {α}

instance BaireMeasurableSpace.instMeasurableSpace : MeasurableSpace (BaireMeasurableSpace α) :=
  EventuallyMeasurableSpace (α := α) (borel _) (residual _)

def BaireMeasurableSet (s : Set α) : Prop := @MeasurableSet (BaireMeasurableSpace _) _ s

variable {s t: Set α}

namespace BaireMeasurableSet

theorem of_mem_residual (h : s ∈ residual _) : BaireMeasurableSet s :=
  eventuallyMeasurableSet_of_mem_filter (α := α) h

theorem _root_.MeasurableSet.baireMeasurableSet [MeasurableSpace α] [BorelSpace α]
    (h : MeasurableSet s) : BaireMeasurableSet s := by
  borelize α
  exact h.eventuallyMeasurableSet

theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h

theorem of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s := MeasurableSet.of_compl h

theorem _root_.IsMeagre.baireMeasurableSet (h : IsMeagre s) : BaireMeasurableSet s :=
  (of_mem_residual h).of_compl

theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i, s i) :=
  MeasurableSet.iUnion h

theorem biUnion {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i ∈ t, s i) :=
  MeasurableSet.biUnion ht h

theorem sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs h

theorem iInter {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i, s i) :=
  MeasurableSet.iInter h

theorem biInter {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i ∈ t, s i) :=
  MeasurableSet.biInter ht h

theorem sInter {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs h

theorem union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∪ t) :=
  MeasurableSet.union hs ht

theorem inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∩ t) :=
  MeasurableSet.inter hs ht

theorem diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s \ t) :=
  MeasurableSet.diff hs ht

theorem congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t :=
  EventuallyMeasurableSet.congr (α := α) hs h.symm

end BaireMeasurableSet

open Filter

theorem MeasurableSet.residualEq_open [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  apply h.induction_on_open (fun s hs => ⟨s, hs, EventuallyEq.rfl⟩)
  . rintro s - ⟨u, uo, su⟩
    refine ⟨(closure u)ᶜ, isClosed_closure.isOpen_compl,
      EventuallyEq.compl (su.trans $ EventuallyLE.antisymm subset_closure.eventuallyLE ?_)⟩
    have : (u ∪ (closure u)ᶜ) ∈ residual _ :=
      residual_of_dense_open (uo.union isClosed_closure.isOpen_compl) union_compl_closure_dense
    rw[EventuallyLE]
    convert this
    simp only [le_Prop_eq, imp_iff_or_not]
    rfl --terrible
  rintro s - - hs
  choose u uo su using hs
  exact ⟨⋃ i, u i, isOpen_iUnion uo, EventuallyEq.countable_iUnion su⟩

theorem BaireMeasurableSet.residualEq_open (h : BaireMeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_open with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

section Map

open Set

variable {f : α → β} (hc : Continuous f) (ho : IsOpenMap f)

theorem Dense.dense_preimage_of_isOpenMap {t : Set β} (ht : Dense t) : Dense (f ⁻¹' t) := by
  rw [dense_iff_closure_eq, ← ho.preimage_closure_eq_closure_preimage hc,
    dense_iff_closure_eq.mp ht, preimage_univ]

theorem residual_map_le_of_isOpenMap : (residual α).map f ≤ residual β := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.dense_preimage_of_isOpenMap hc ho)

theorem IsMeagre.preimage_of_isOpenMap {s : Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s) :=
  residual_map_le_of_isOpenMap hc ho h

theorem BaireMeasurableSet.preimage {s : Set β} (h : BaireMeasurableSet s) :
    BaireMeasurableSet (f⁻¹' s) := by
  rcases h with ⟨u, hu, hsu⟩
  refine ⟨f ⁻¹' u, ?_, hsu.filter_mono <| residual_map_le_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu

theorem Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β := by
  refine' le_antisymm (residual_map_le_of_isOpenMap h.continuous h.isOpenMap) (le_map _)
  simp_rw[← preimage_symm]
  exact residual_map_le_of_isOpenMap h.symm.continuous h.symm.isOpenMap

end Map
