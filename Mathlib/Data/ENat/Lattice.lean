/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.enat.lattice
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.
-/

-- porting notes: was `deriving instance` but "default handlers have not been implemented yet"
-- porting notes: `noncomputable` through 'Nat.instConditionallyCompleteLinearOrderBotNat'
noncomputable instance : CompleteLinearOrder ENat :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℕ))

-- open Order in
-- lemma WithTop.supₛ_lt_coe {α : Type _} [ConditionallyCompleteLinearOrderBot α] [PredOrder α]
--     {s : Set (WithTop α)} {a : α} (h : s.Nonempty ∨ a ≠ ⊥) : supₛ s < a ↔ ∀ x ∈ s, x < a := by
--   refine ⟨fun h x hx => (le_supₛ hx).trans_lt h, fun hs => ?_⟩
--   calc supₛ s ≤ pred a := supₛ_le fun x hx => by
--   { rcases lt_iff_exists_coe.1 (hs x hx) with ⟨x, rfl, hx'⟩
--     exact coe_le_coe.2 (le_pred_of_lt <| coe_lt_coe.1 hx') }
--   _ < a := coe_lt_coe.2 <| pred_lt_iff_ne_bot.2 <| h.symm.elim id <| by
--   { rintro ⟨x, hx⟩ rfl; exact not_lt_bot (hs x hx) }

-- namespace ENat

-- lemma supₛ_lt_coe {s : Set ℕ∞} {n : ℕ} (h : s.Nonempty ∨ n ≠ 0) : supₛ s < n ↔ ∀ k ∈ s, k < n := by
--   refine ⟨fun h k hk => (le_supₛ hk).trans_lt h, fun hs => ?_⟩
--   have hn : 0 < n := h.elim (fun ⟨k, hk⟩ => WithTop.coe_pos.1 (bot_le.trans_lt (hs k hk)))
--     Nat.pos_of_ne_zero


-- lemma coe_le_supₛ {s : Set ℕ∞} {n : ℕ} : ↑n ≤ supₛ s ↔ ∃ k ∈ s, ↑n ≤ k := by
--   _

-- end ENat
