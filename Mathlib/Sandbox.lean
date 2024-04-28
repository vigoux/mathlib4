import Mathlib.Analysis.NormedSpace.PiLp

noncomputable section

instance PiLp.seminormedRing (p : ENNReal) {ι : Type*} (β : ι → Type*) [Fact (1 ≤ p)] [Fintype ι]
    [(i : ι) → SeminormedRing (β i)] :
    SeminormedRing (PiLp p β) :=
  { Pi.ring, PiLp.seminormedAddCommGroup p β with
    norm_mul := by
      intro _ _
      obtain (rfl | h) := p.dichotomy
      · simp_rw [norm_eq_ciSup]
        sorry
      · have hp : 0 < p.toReal := sorry
        simp_rw [norm_eq_sum hp]
        rw [← Real.mul_rpow, Finset.sum_mul_sum]
        simp_rw [← Real.mul_rpow sorry sorry]

        sorry
  }

instance PiLp.normedRing (p : ENNReal) {ι : Type*} (β : ι → Type*) [Fact (1 ≤ p)] [Fintype ι]
    [(i : ι) → NormedRing (β i)] :
    NormedRing (PiLp p β) :=
  { Pi.ring with
    dist_eq := sorry
    norm_mul := sorry

  }

instance PiLp.normedCommRing (p : ENNReal) {ι : Type*} (β : ι → Type*) [Fact (1 ≤ p)] [Fintype ι]
    [(i : ι) → NormedCommRing (β i)] :
    NormedCommRing (PiLp p β) := sorry

