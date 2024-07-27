import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  NumberField.Units

open scoped Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable (K) in
def fullBasis : InfinitePlace K → (InfinitePlace K → ℝ) := by
  intro i
  by_cases hi : i = w₀
  · exact fun w ↦ (mult w : ℝ)
  · exact fun w ↦ mult w * Real.log (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)))

example : LinearIndependent ℝ (fullBasis K) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  
