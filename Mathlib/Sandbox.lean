import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.Algebra.Module.Zlattice.Covolume

section IsZlattice

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] (L : AddSubgroup E) [DiscreteTopology L]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
variable [ProperSpace F]
variable (f : E →+ F)

end IsZlattice


variable (K : Type*) [Field K] [NumberField K]

open Classical

open Filter NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Topology MeasureTheory
  NumberField.Units NumberField.mixedEmbedding.fundamentalCone

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

def A : Set (E K) := {x ∈ fundamentalCone K | mixedEmbedding.norm x ≤ 1}

example :
    Tendsto (fun n : ℝ ↦
      Nat.card {I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n} *
      torsionOrder K / n) atTop
      (𝓝 ((volume (A K)).toReal)) := by
  
  have := Zlattice.covolume.tendsto_card_le_div


  sorry
