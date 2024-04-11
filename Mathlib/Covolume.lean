import Mathlib.UnitBox
import Mathlib.FundamentalCone

noncomputable section

open Submodule Fintype Bornology Filter Topology MeasureTheory

open scoped Pointwise

variable {E ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (X : Set E) (hX : ∀ ⦃x : E⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x | F x ≤ 1})

open Submodule

example {B : ℝ} (hB : 0 < B) :
    Nat.card ({x ∈ X  | F x ≤ B ^ card ι} ∩ span ℤ (Set.range b) : Set E) =
      Nat.card ({x ∈ X | F x ≤ 1 } ∩ B⁻¹ • (span ℤ (Set.range b)) : Set E) := by
  have hB₂ : 0 ≤ B⁻¹ := inv_nonneg.mpr (le_of_lt hB)
  have hB₃ : B⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hB)
  refine Nat.card_congr <| Equiv.subtypeEquiv (Equiv.smulRight hB₃) (fun a ↦ ?_)
  simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀
    hB₃, SetLike.mem_coe, hF₁ a hB₂, inv_pow, inv_mul_le_iff (pow_pos hB _), mul_one,
    and_congr_left_iff]
  refine fun _ _ ↦ ⟨fun h ↦ hX h hB₂, fun h ↦ ?_⟩
  convert hX h (le_of_lt hB)
  rw [smul_inv_smul₀ (ne_of_gt hB)]

example :
    Tendsto (fun n : ℕ ↦
      Nat.card ({x ∈ X  | F x ≤ n} ∩ span ℤ (Set.range b) : Set E) / (n : ℝ))
      atTop (𝓝 (volume (b.equivFun ''  {x | F x ≤ 1})).toReal) := sorry
