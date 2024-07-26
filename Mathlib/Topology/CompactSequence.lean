/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Topology.Instances.ENat

/-!
# Compactified sequence

In this file we define `compactSequence f a`. Given `f : ℕ → α` and `a : α`,
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

open Set Filter Topology

variable {α : Type*} {f : ℕ → α} {a : α}

/-- Given a sequence `f : ℕ → α` and `a : α`, `compactSequence f a : ℕ∞ → α` corresponds
to the extension of `f` sending `⊤` to `a`. If `f` tendsto `a` then
`compactSequence f a` is continuous (see `continuous_compactSequence_iff`)
and therefore has compact range (`isCompact_range_compactSequence`). -/
def compactSequence (f : ℕ → α) (a : α) : ℕ∞ → α := fun n ↦
  match n with
  | some k => f k
  | none => a

theorem compactSequence_coe (n : ℕ) : compactSequence f a n = f n := rfl

theorem compactSequence_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : compactSequence f a n = f n.toNat := by
  lift n to ℕ using hn
  rfl

theorem compactSequence_top : compactSequence f a ⊤ = a := rfl

theorem range_compactSequence : range (compactSequence f a) = insert a (range f) := by
  ext b
  constructor
  · rintro ⟨n, rfl⟩
    rcases eq_or_ne n ⊤ with rfl | hn
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨n.toNat, (compactSequence_ne_top hn).symm⟩
  · rw [mem_insert_iff]
    rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨⊤, rfl⟩
    · exact ⟨n, rfl⟩

variable [TopologicalSpace α]

theorem continuous_compactSequence_iff :
    Continuous (compactSequence f a) ↔ Tendsto f atTop (𝓝 a) where
  mp h := by
    refine tendsto_atTop_nhds.2 fun U ha hU ↦ ?_
    have := tendsto_nhds.1 (h.tendsto' ⊤ a compactSequence_top) U hU ha
    rcases (nhds_top_basis.mem_iff' _).1 this with ⟨N, hN, h'⟩
    lift N to ℕ using hN.ne
    refine ⟨N + 1, fun n hn ↦ ?_⟩
    rw [← @compactSequence_coe _ f a]
    apply h'
    simp only [mem_Ioi, Nat.cast_lt]
    omega
  mpr h := by
    refine continuous_def.2 fun s hs ↦ ?_
    by_cases htop : ⊤ ∈ (compactSequence f a ⁻¹' s)
    · rw [isOpen_iff_top_mem _ htop]
      rcases tendsto_atTop_nhds.1 h s htop hs with ⟨N, hN⟩
      refine ⟨N, fun y hy ↦ ?_⟩
      rcases eq_or_ne y ⊤ with rfl | y_ne_top
      · exact htop
      · lift y to ℕ using y_ne_top
        exact hN _ (by simpa using hy : N < y).le
    · exact isOpen_top_not_mem _ htop

theorem isCompact_range_compactSequence (h : Tendsto f atTop (𝓝 a)) :
    IsCompact (range (compactSequence f a)) :=
  isCompact_range (continuous_compactSequence_iff.2 h)
