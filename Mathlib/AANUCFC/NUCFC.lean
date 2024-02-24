import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Algebra.Algebra.Unitization

namespace Unitization

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

lemma isUnit_fst {x : Unitization R A} (hx : IsUnit x) : IsUnit x.fst :=
  hx.map <| fstHom R A

lemma isUnit_of_fst_one (x : (Unitization R A)ˣ) (hx_fst : x.val.fst = 1) :
    x.val.snd + x⁻¹.val.snd + x.val.snd * x⁻¹.val.snd = 0 := by
  have := congr($(x.mul_inv).snd)
  simp [-Units.mul_inv, snd_one, hx_fst] at this

  sorry

#exit

end Unitization
namespace v1

def quasiSpectrum (R : Type*) {A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (a : A) : Set R :=
  { r : R | ¬ ∃ b, r⁻¹ • a + b = r⁻¹ • a * b ∧ r⁻¹ • a + b = b * r⁻¹ • a }

variable (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A]

namespace quasiSpectrum

lemma quasiSpectrum_eq (a : A) : quasiSpectrum R a = spectrum R a := by
  ext r
  constructor
  · rintro ⟨b, hb₁, hb₂⟩

    sorry
  · sorry
#exit

-- 1 = (1 - r⁻¹ • a) * b = b - r⁻¹ • a * b
-- set b = 1 - c, then we find 1 = (1 - c) - r⁻¹ • a * (1 - c) = 1 - c - r⁻¹ • a + r⁻¹ • a * c


-- so, if `b` is the unit in `A₁`, then `1 - c` is the unit in `A`.

-- 1 = b * (1 - r⁻¹ • a) = b - r⁻¹ • b * a

  -- [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

-- yuck we need `Semifield`

end v1

namespace v2

abbrev spectrumₙ (R : Type*) {S : outParam Type*} {A : Type*} [CommSemiring R] [CommRing S]
    [NonUnitalRing A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S] [DistribMulAction R A] [IsScalarTower R S A] (a : A) : Set R :=
  spectrum R (a : Unitization S A)

variable (R : Type*) {S A : Type*} [CommSemiring R] [CommRing S]
    [NonUnitalRing A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S] [DistribMulAction R A] [IsScalarTower R S A] (a : A)

variable (a : A)

end v2

#exit

/-
plan:

1. define the quasispectrum (over a semifield) and show that it is equal to the spectrum when the
  ring is unital.
2. define the nonunital cfc class in terms of this.



-/
