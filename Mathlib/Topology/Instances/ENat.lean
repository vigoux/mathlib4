/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.Order.Compact

/-!
# Topology on extended natural numbers

In this file we define on topology on `ℕ∞`, which is the order toplogy. It corresponds to the
one-point compactification of `ℕ`. Compactness and Hausdorff are inferred by typeclass inference.

We prove that any set not containing `⊤` is open, and that a set containing `⊤` is open
if and only if it contains `Ioi ↑n`, for `n : ℕ`.

We then use this topology to define `compactSequence f a`. Given `f : ℕ → α` and `a : α`,
`compactSequence f a : ℕ∞ → α` is the extension of `f` which sends `⊤` to `a`. This function
is continuous if and only if `f` tends to `a`. This is useful to prove that a `SequentialSpace`
is a `CompactlyGeneratedSpace`.

## Main definitions
* `compactSequence f a`: Given `f : ℕ → α` and `a : α`, `compactSequence f a : ℕ∞ → α`
  is the extension of `f` which sends `⊤` to `a`.

## Main statements
* `continuous_compactSequence_iff`: `compactSequence f a` is continuous if and only if
  `f` tends to `a`.
-/

open ENat Filter Topology TopologicalSpace Set

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := OrderTopology.mk rfl

theorem isOpen_singleton_coe (n : ℕ) : IsOpen {(n : ℕ∞)} := by
  cases n with
  | zero =>
    refine GenerateOpen.basic _ ⟨1, Or.inr ?_⟩
    ext i
    simp only [ENat.coe_zero, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact lt_one_iff_eq_zero.symm
  | succ k =>
    have : {(↑(k + 1) : ℕ∞)} = (Set.Iio ↑(k + 2)) ∩ (Set.Ioi ↑k) := by
      rw [Iio_inter_Ioi]
      ext i
      simp only [mem_singleton_iff, mem_Ioo]
      rcases eq_or_ne i ⊤ with h | h
      · simp only [h, not_top_lt, and_false, iff_false]
        exact top_ne_coe _
      · lift i to ℕ using h
        norm_cast
        omega
    rw [this]
    apply GenerateOpen.inter <;> constructor
    · exact ⟨(↑(k + 2) : ℕ∞), Or.inr rfl⟩
    · exact ⟨k, Or.inl rfl⟩

theorem isOpen_singleton_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : IsOpen {n} := by
  lift n to ℕ using hn
  exact isOpen_singleton_coe _

theorem isOpen_top_not_mem (s : Set ℕ∞) (h : ⊤ ∉ s) : IsOpen s := by
  rw [← Set.biUnion_of_singleton s]
  exact isOpen_biUnion fun x hx ↦ isOpen_singleton_ne_top <| ne_of_mem_of_not_mem hx h

theorem isOpen_iff_top_mem (s : Set ℕ∞) (top_mem : ⊤ ∈ s) :
    IsOpen s ↔ ∃ n : ℕ, Set.Ioi ↑n ⊆ s where
  mp hs := by
    rcases (nhds_top_basis.mem_iff' s).1 (hs.mem_nhds top_mem) with ⟨n, n_lt, hn⟩
    lift n to ℕ using n_lt.ne
    exact ⟨n, hn⟩
  mpr := by
    rintro ⟨a, ha⟩
    rw [← Set.inter_union_compl s (Set.Ioi a)]
    apply IsOpen.union
    · rw [Set.inter_eq_self_of_subset_right ha]
      exact GenerateOpen.basic _ ⟨a, Or.inl rfl⟩
    · apply isOpen_top_not_mem
      simp [top_mem]

theorem ENat.tendsto_coe_atTop :
    Tendsto (@Nat.cast ℕ∞ _) atTop (𝓝 ⊤) := by
  rw [tendsto_atTop_nhds]
  intro U mem_U hU
  rcases (isOpen_iff_top_mem _ mem_U).1 hU with ⟨N, hU⟩
  refine ⟨N + 1, fun n hn ↦ hU ?_⟩
  simp only [Set.mem_Ioi, Nat.cast_lt]
  omega
