import Mathlib.Sandbox
import Mathlib.FundamentalCone

noncomputable section

open Submodule Fintype Bornology

open scoped Pointwise

variable {E ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

variable (X : Set E) (hX : ∀ ⦃x : E⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)

variable (F : E → ℝ) (hF₁ : ∀ (x : E) ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x | F x ≤ 1})

open Submodule

abbrev Nbr (B : ℝ) := Nat.card {x ∈ X ∩ (span ℤ (Set.range b)) | F x ≤ B }

example {B : ℝ} (hB : 0 < B) :
    Nbr b X F (B ^ card ι) =
      Nat.card ({x ∈ X | F x ≤ 1 } ∩ B⁻¹ • (span ℤ (Set.range b)) : Set E) := by
  have hB₂ : 0 ≤ B⁻¹ := inv_nonneg.mpr (le_of_lt hB)
  refine Nat.card_congr ?_
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · exact B⁻¹ • x
    · refine hX hx₁ hB₂
    · specialize hF₁ x hB₂
      rw [hF₁]
      rw [inv_pow]
      rwa [inv_mul_le_iff, mul_one]
      refine pow_pos hB _
    · exact Set.smul_mem_smul_set hx₂
  · dsimp
    sorry
  · sorry
