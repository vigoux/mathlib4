/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.
-/

open Set

-- Porting note: was `deriving instance` but "default handlers have not been implemented yet"
-- Porting note: `noncomputable` through 'Nat.instConditionallyCompleteLinearOrderBotNat'
noncomputable instance : CompleteLinearOrder ENat :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℕ))

namespace ENat
variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

lemma iSup_coe_eq_top : ⨆ i, (f i : ℕ∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
lemma iSup_coe_ne_top : ⨆ i, (f i : ℕ∞) ≠ ⊤ ↔ BddAbove (range f) := iSup_coe_eq_top.not_left
lemma iSup_coe_lt_top : ⨆ i, (f i : ℕ∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
lemma iInf_coe_eq_top : ⨅ i, (f i : ℕ∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
lemma iInf_coe_ne_top : ⨅ i, (f i : ℕ∞) ≠ ⊤ ↔ Nonempty ι := by
  rw [Ne, iInf_coe_eq_top, not_isEmpty_iff]
lemma iInf_coe_lt_top : ⨅ i, (f i : ℕ∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

lemma coe_sSup : BddAbove s → ↑(sSup s) = ⨆ a ∈ s, (a : ℕ∞) := WithTop.coe_sSup

lemma coe_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a ∈ s, (a : ℕ∞) :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

lemma coe_iSup : BddAbove (range f) → ↑(⨆ i, f i) = ⨆ i, (f i : ℕ∞) := WithTop.coe_iSup _

@[norm_cast] lemma coe_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : ℕ∞) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

@[simp]
lemma iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : ℕ∞) = ⊤ :=
  iInf_coe_eq_top.mpr ‹_›

lemma iInf_toNat : (⨅ i, (f i : ℕ∞)).toNat = ⨅ i, f i := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

lemma iInf_eq_zero : ⨅ i, (f i : ℕ∞) = 0 ↔ ∃ i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast
    rw [iInf, Nat.sInf_eq_zero]
    exact ⟨fun h ↦ by simp_all, .inl⟩

variable {f : ι → ℕ∞} {s : Set ℕ∞}

lemma sSup_eq_zero : sSup s = 0 ↔ ∀ a ∈ s, a = 0 :=
  sSup_eq_bot

lemma sInf_eq_zero : sInf s = 0 ↔ 0 ∈ s := by
  rw [← lt_one_iff_eq_zero]
  simp only [sInf_lt_iff, lt_one_iff_eq_zero, exists_eq_right]

lemma sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0} :=
  sSup_eq_bot'

lemma iSup_add (ι : Type*) [Nonempty ι] (f : ι → ℕ∞) (n : ℕ∞) :
    (⨆ x, f x) + n = (⨆ x, f x + n) := by
  apply le_antisymm
  · cases n; simp; next n =>
    apply le_iSup_iff.mpr
    intro m hm
    cases m; simp; next m =>
    have hnm : n ≤ m := by
      obtain i : ι := Classical.ofNonempty
      specialize hm i
      revert hm
      cases f i; simp; next i =>
      intro h; norm_cast at h; omega
    suffices (⨆ x, f x) ≤ ↑(m - n) by
      revert this
      cases (⨆ x, f x)
      · simp only [top_le_iff, coe_ne_top, false_imp_iff]
      · norm_cast; omega
    apply iSup_le
    intro i
    specialize hm i
    revert hm
    cases f i <;> intro hm
    · exfalso; simp at hm
    · norm_cast at *; omega
  · apply Monotone.le_map_iSup (f := (· + n))
    exact Monotone.add_const (fun ⦃a b⦄ h ↦ h) n

end ENat
